# bennett-pebble

**Pebble**: a design, with proofs and a working model, for an optimising,
pebbling circuit compiler for Bennett ISA 0.9 lifted oracles. It is the design
behind the plan item "optimising specialiser and scheduler" (bead
`bennett-p2i`) in the Bennett workspace.

Research status, not production code. Start with `HANDOFF.md`.

| Path | What | Status |
|---|---|---|
| `HANDOFF.md` | Everything done, what is checked, what is open, how to merge | read first |
| `docs/DESIGN.md` | The compiler design (pipeline, cost model, ISA conformance, kernel scale, results) | complete |
| `docs/CORE.md` | Formal core: definitions and statements (revision 2) | complete |
| `docs/THEORY.md` | Analytic proofs and corrections | complete |
| `formal/` | Lean 4 mechanisation, 65 theorems, no `sorry` | builds clean |
| `model/` | Rust executable model: parser, reference interpreter, compiler, chain-game solver, verification, measurements | 39 tests pass; memory-free subset |
| `theory/` | Python scripts behind the chain-game tables | reproducible |
| `fixtures/` | `.bobj` inputs (Collatz, gcd, popcount, …) | — |
| `ref/isa-spec/SNAPSHOT_REV` | The `bennett-isa-spec` commit all `§n` references point at | spec copy not committed |

## Reproduce

```sh
# model
cd model && cargo test --offline && cargo run --release --offline && python3 report.py
cargo run --release --offline -- --one collatz 2048 10545        # one cost record
cargo run --release --offline -- --emit collatz 28 | head        # flat gate stream
cargo run --release --offline -- --hierarchy collatz 1000000000 10000 > c.pcirc

# Lean (elan is installed in ~/.elan and is not on PATH)
cd formal && ~/.elan/bin/lake build

# chain-game tables
cd theory && python3 chain_search.py && python3 kary_frontier.py
```

To restore the spec snapshot the documents cite:

```sh
mkdir -p ref/isa-spec && git -C ../bennett-workspace/bennett-isa-spec archive \
  "$(cat ref/isa-spec/SNAPSHOT_REV)" spec include README.md | tar -x -C ref/isa-spec
```
