#!/usr/bin/env python3
"""Optional standard-library renderer for the measured research report."""
from pathlib import Path
import csv
import json

root = Path(__file__).resolve().parent
results = root / "results"
measurements = json.loads((results / "measurements.json").read_text())
chain = json.loads((results / "chain.json").read_text())
verification = list(csv.DictReader((results / "verification-boundaries.csv").open()))
residues = list(csv.DictReader((results / "residue.csv").open()))
planning = json.loads((results / "uniform-1e9.json").read_text())

def table(headers, rows):
    return "\n".join(["| " + " | ".join(headers) + " |", "|" + "---|" * len(headers)] + ["| " + " | ".join(map(str, row)) + " |" for row in rows])

def number(n):
    return f"{n:,}"

residue_table = table(["Fixture", "State before", "State after", "Residue before", "Residue after", "Rank", "Data residue"], [[r[k] for k in ("fixture", "baseline_state_bits", "optimized_state_bits", "baseline_residue_bits", "optimized_residue_bits", "rank_bits", "data_residue_bits")] for r in residues])
blocks = []
for fixture in dict.fromkeys(r["fixture"] for r in measurements):
    rows = []
    for r in measurements:
        if r["fixture"] != fixture:
            continue
        if r["status"] != "ok":
            raise RuntimeError(r)
        h = {int(k): v for k, v in r["histogram"].items()}
        rows.append([number(r["B"]), "unlimited" if r["peak_qubit_budget"] is None else number(r["peak_qubit_budget"]), number(r["peak_qubits"]), number(h.get(0, 0)), number(h.get(1, 0)), number(h.get(2, 0)), number(sum(v for k, v in h.items() if k >= 3)), number(r["toffoli_equiv"]), number(r["total_gates"]), f'{r["compile_us"]/1000:.3f}', f'{r["peak_rss_kib"]/1024:.3f}'])
    blocks.append("### " + fixture + "\n\n" + table(["B", "Peak budget", "Qubits", "X", "CX", "CCX", "MCX", "Toffoli eq.", "Native gates", "Compile ms", "RSS MiB"], rows))

scaling_rows = []
for b in (9, 28, 100, 2048, 10**6, 10**9):
    rows = [r for r in measurements if r["fixture"] == "collatz" and r["B"] == b]
    u = next(r for r in rows if r["peak_qubit_budget"] is None)
    tight = min((r for r in rows if r["peak_qubit_budget"] is not None), key=lambda r: r["peak_qubit_budget"])
    scaling_rows.append([number(b), number(u["dag_nodes"]), number(tight["dag_nodes"]), f'{u["compile_us"]/1000:.3f}', f'{tight["compile_us"]/1000:.3f}', f'{u["peak_rss_kib"]/1024:.3f}', f'{tight["peak_rss_kib"]/1024:.3f}'])
scaling = "The following is the measured Collatz description/compilation scaling, with the tightest fixed quota beside unlimited space. B grows by more than eight orders of magnitude. Term count, compile time and RSS do not grow linearly with B. Counter widths and nested-definition levels grow logarithmically; the measurements are not a claim of strict constant time or memory.\n\n" + table(["B", "Unlimited DAG nodes", "Tight DAG nodes", "Unlimited ms", "Tight ms", "Unlimited RSS MiB", "Tight RSS MiB"], scaling_rows)

plan_text = f'The separate T=10^9 planning/checking benchmark ran {planning["iterations"]:,} iterations in {planning["total_us"]:,} µs: mean {planning["mean_ns"]:,} ns per plan plus check. It selected leaf {planning["leaf"]:,}, levels {planning["levels"]}, padded length {planning["scheduled"]:,}, and checked peak {planning["peak"]:,} for m=72, r=2, S=4096. This is a scalar-descriptor benchmark, separate from complete compiler timings. See `uniform-1e9.json`.'
substitutions = {
    "TESTS": "39",
    "BOUNDARY_RUNS": number(len(verification)),
    "BOUNDARY_CASES": number(sum(int(r["interface_cases"]) for r in verification)),
    "GAP": str(chain["largest_additive_gap"]),
    "MISSES": str(chain["nested_reachability_misses"]),
    "CHAIN_INSTANCES": str(chain["instances"]),
    "MEASUREMENTS": str(len(measurements)),
    "RESIDUE_TABLE": residue_table,
    "PLANNING": plan_text,
    "SCALING": scaling,
    "MEASUREMENT_TABLES": "\n\n".join(blocks),
}
text = (root / "RESULTS.template.md").read_text()
for key, value in substitutions.items():
    text = text.replace("{{" + key + "}}", value)
if "{{" in text:
    raise RuntimeError("unexpanded report field")
if any(r["status"] != "pass" for r in verification):
    raise RuntimeError("failed verification row")
(root / "RESULTS.md").write_text(text)
