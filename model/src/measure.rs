use crate::{
    bits::Bits,
    chain, circuit,
    compiler::Compiled,
    source::{Budget, Program},
};
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};
pub const FIXTURES: &[&str] = &[
    "inc8",
    "collatz",
    "gcd",
    "popcount",
    "diamond",
    "irreducible",
    "faultif",
];
pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).to_path_buf()
}
pub fn load(name: &str) -> Result<Program, String> {
    Program::parse(
        &fs::read_to_string(root().join("../fixtures").join(format!("{name}.bobj")))
            .map_err(|e| e.to_string())?,
    )
}
pub fn budget(p: &Program, steps: u64) -> Budget {
    Budget {
        steps,
        heap: 0,
        stack: p
            .layout
            .map_or(0, |s| 32u64.min(1u64.checked_shl(s).unwrap_or(u64::MAX))),
        depth: if p.layout.is_some() { 32 } else { 0 },
    }
}
fn rss() -> u64 {
    fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .and_then(|l| l.split_whitespace().nth(1)?.parse().ok())
        })
        .unwrap_or(0)
}
pub fn one(name: &str, steps: u64, cap: Option<usize>) -> Result<String, String> {
    let started = Instant::now();
    let p = load(name)?;
    let b = budget(&p, steps);
    let out = Compiled::best(&p, b, true, cap);
    let us = started.elapsed().as_micros();
    let rss = rss();
    let capstr = cap.map_or("null".into(), |n| n.to_string());
    match out {
        Ok(c) => {
            let (nodes, maps) = circuit::dag_stats(&c.term);
            let datapath = if c.residue_width == c.state_width {
                "full_state_history"
            } else if c.cost.histogram.keys().max().copied().unwrap_or(0) > 2 {
                "residue_inplace_inverse"
            } else {
                "residue_xor_inverse"
            };
            let strategy = if c.checkpoints == 0 {
                "history"
            } else {
                "regular_nested"
            };
            let hist = c
                .cost
                .histogram
                .iter()
                .map(|(k, n)| format!("\"{k}\":{n}"))
                .collect::<Vec<_>>()
                .join(",");
            Ok(format!(
                "{{\"fixture\":\"{name}\",\"B\":{steps},\"peak_qubit_budget\":{capstr},\"status\":\"ok\",\"method\":\"structural_cost_recursion\",\"simulation\":false,\"datapath\":\"{datapath}\",\"strategy\":\"{strategy}\",\"peak_qubits\":{},\"dag_nodes\":{nodes},\"wire_map_entries\":{maps},\"native_peak_wires\":{},\"toffoli_equiv\":{},\"total_gates\":{},\"steps_executed\":{},\"checkpoints\":{},\"state_width\":{},\"residue_width\":{},\"scheduled_chain_length\":{},\"histogram\":{{{hist}}},\"compile_us\":{us},\"peak_rss_kib\":{rss}}}",
                c.cost.peak(c.external),
                c.external + c.cost.extra_peak,
                c.cost.toffoli(),
                c.cost.total(),
                c.step_invocations,
                c.checkpoints,
                c.state_width,
                c.residue_width,
                c.steps
            ))
        }
        Err(e) => Ok(format!(
            "{{\"fixture\":\"{name}\",\"B\":{steps},\"peak_qubit_budget\":{capstr},\"status\":\"infeasible\",\"reason\":\"{}\",\"compile_us\":{us},\"peak_rss_kib\":{rss}}}",
            e.replace('"', "'")
        )),
    }
}
fn field<'a>(json: &'a str, key: &str) -> Option<&'a str> {
    let needle = format!("\"{key}\":");
    let begin = json.find(&needle)? + needle.len();
    Some(json[begin..].split([',', '}']).next()?.trim_matches('"'))
}
pub fn measurements() -> Result<(), String> {
    let dir = root().join("results");
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let mut csv = fs::File::create(dir.join("tradeoff.csv")).map_err(|e| e.to_string())?;
    writeln!(csv,"fixture,B,peak_qubit_budget,peak_qubits,toffoli_equiv,total_gates,steps_executed,checkpoints").map_err(|e|e.to_string())?;
    let mut residues = String::from(
        "fixture,B,baseline_state_bits,optimized_state_bits,baseline_residue_bits,optimized_residue_bits,rank_bits,data_residue_bits\n",
    );
    let mut json = vec![];
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    for name in FIXTURES {
        let p = load(name)?;
        let b = budget(&p, 1_000_000_000);
        let c = Compiled::optimized(&p, b, true)?;
        let (workspace, ladder, _) = c.auxiliary();
        let compact = Compiled::optimized_compact(&p, b, true)?;
        let (compact_workspace, compact_ladder, _) = compact.auxiliary();
        let fixed = c.external + (workspace + ladder).min(compact_workspace + compact_ladder);
        let baseline = Compiled::baseline(&p, b, true)?;
        residues += &format!(
            "{name},1000000000,{},{},{},{},{},{}\n",
            baseline.state_width,
            c.state_width,
            baseline.residue_width,
            c.residue_width,
            c.layout.pc.len(),
            c.residue_width - c.layout.pc.len()
        );
        let caps: Vec<_> = [36, 64, 128, 512]
            .into_iter()
            .map(|n| Some(fixed + n * c.state_width))
            .collect();
        for steps in [9, 28, 100, 2048, 1_000_000, 1_000_000_000] {
            for cap in std::iter::once(None).chain(caps.iter().copied()) {
                let mut cmd = Command::new(&exe);
                cmd.args([
                    "--one",
                    name,
                    &steps.to_string(),
                    &cap.map_or("unlimited".into(), |v| v.to_string()),
                ]);
                let output = cmd.output().map_err(|e| e.to_string())?;
                if !output.status.success() {
                    return Err(String::from_utf8_lossy(&output.stderr).into());
                }
                let line = String::from_utf8(output.stdout)
                    .map_err(|e| e.to_string())?
                    .trim()
                    .to_string();
                let captext = cap.map_or("unlimited".into(), |v| v.to_string());
                let values = [
                    "peak_qubits",
                    "toffoli_equiv",
                    "total_gates",
                    "steps_executed",
                    "checkpoints",
                ]
                .map(|k| field(&line, k).unwrap_or(""));
                writeln!(
                    csv,
                    "{name},{steps},{captext},{},{},{},{},{}",
                    values[0], values[1], values[2], values[3], values[4]
                )
                .map_err(|e| e.to_string())?;
                json.push(line);
            }
        }
        eprintln!("measured {name}");
    }
    fs::write(dir.join("residue.csv"), residues).map_err(|e| e.to_string())?;
    fs::write(
        dir.join("measurements.json"),
        format!("[\n{}\n]\n", json.join(",\n")),
    )
    .map_err(|e| e.to_string())?;
    Ok(())
}
pub fn chain_study() -> Result<(), String> {
    let mut count = 0;
    let mut misses = 0;
    let mut largest = 0u128;
    let mut ratio = 1.0f64;
    let mut worst = String::new();
    let mut table = String::from("kind,T,m,r,space,exact,nested,states\n");
    let mut compare = |kind: &str, g: chain::Game| -> Result<(), String> {
        let exact = chain::exact(&g, 500_000)?;
        let nested = chain::nested(&g);
        count += 1;
        if let Some(n) = &nested {
            let mut moves = vec![];
            n.moves(false, &mut moves);
            let cert = chain::replay(&g, moves)?;
            if cert.cost != n.cost {
                return Err("nested price does not match replay".into());
            }
        }
        if let Some(a) = &exact {
            if let Some(b) = &nested {
                if b.cost < a.cost {
                    return Err("nested beats exact solver: bug".into());
                }
                let gap = b.cost - a.cost;
                ratio = ratio.max(b.cost as f64 / a.cost.max(1) as f64);
                if gap > largest {
                    largest = gap;
                    let mut path = vec![];
                    b.moves(false, &mut path);
                    worst = format!(
                        "game={g:?}\nexact_cost={}\nnested_cost={}\nexact={:?}\nnested={path:?}\n",
                        a.cost, b.cost, a.moves
                    );
                }
            } else {
                misses += 1;
            }
        }
        table += &format!(
            "{kind},{},{},{},{},{},{},{}\n",
            g.t(),
            g.m[0],
            g.r.first().unwrap_or(&0),
            g.space,
            exact
                .as_ref()
                .map_or("unreachable".into(), |a| a.cost.to_string()),
            nested
                .as_ref()
                .map_or("unreachable".into(), |b| b.cost.to_string()),
            exact.as_ref().map_or(0, |a| a.explored)
        );
        Ok(())
    };
    for t in 1..=6 {
        for m in 1..=2 {
            for r in 0..=2 {
                for space in m..=10 {
                    compare("uniform", chain::Game::uniform(t, m, r, 2, 1, space))?;
                }
            }
        }
    }
    for seed in 0..32 {
        let mut g = chain::Game::uniform(5, 1, 1, 1, 1, 10);
        for j in 0..=g.t() {
            g.m[j] = 1 + ((seed >> (j % 4)) & 1);
            g.k[j] = 1 + (j % 2) as u64;
        }
        for j in 0..g.t() {
            g.r[j] = (seed + j as u64) % 3;
            g.a[j] = 1 + (j % 3) as u64;
        }
        compare("nonuniform", g)?;
    }
    let plan_started = Instant::now();
    let iterations = 10_000u64;
    for _ in 0..iterations {
        let p = chain::uniform(std::hint::black_box(1_000_000_000), 72, 2, 100, 72, 4096)
            .ok_or("uniform benchmark not found")?;
        chain::check_uniform(&p, 72, 2, 100, 72, 4096)?;
        std::hint::black_box(p);
    }
    let elapsed = plan_started.elapsed();
    let uniform = chain::uniform(1_000_000_000, 72, 2, 100, 72, 4096).unwrap();
    let planning = format!(
        "{{\"T\":1000000000,\"m\":72,\"r\":2,\"space\":4096,\"a\":100,\"k\":72,\"leaf\":{},\"levels\":{},\"scheduled\":{},\"peak\":{},\"cost\":{},\"iterations\":{iterations},\"total_us\":{},\"mean_ns\":{},\"checked\":true}}\n",
        uniform.leaf,
        uniform.levels,
        uniform.scheduled,
        uniform.peak,
        uniform.cost,
        elapsed.as_micros(),
        elapsed.as_nanos() / u128::from(iterations)
    );
    let dir = root().join("results");
    fs::write(dir.join("uniform-1e9.json"), planning).map_err(|e| e.to_string())?;
    fs::write(dir.join("chain.csv"), table).map_err(|e| e.to_string())?;
    fs::write(
        dir.join("chain-worst.txt"),
        if worst.is_empty() {
            "No nonzero gap was found among the recorded finite instances.\n".into()
        } else {
            worst
        },
    )
    .map_err(|e| e.to_string())?;
    fs::write(dir.join("chain.json"),format!("{{\"instances\":{count},\"largest_additive_gap\":{largest},\"largest_ratio\":{ratio},\"nested_reachability_misses\":{misses},\"optimality_scope\":\"exact Dijkstra for listed finite instances; nested DP only within documented grammar\"}}\n")).map_err(|e|e.to_string())?;
    Ok(())
}
pub fn verification(boundaries: bool) -> Result<(), String> {
    let dir = root().join("results");
    let filename = if boundaries {
        "verification-boundaries.csv"
    } else {
        "verification.csv"
    };
    let mut csv = fs::File::create(dir.join(filename)).map_err(|e| e.to_string())?;
    writeln!(
        csv,
        "fixture,B,mode,controlled,interface_cases,checkpoints,wall_ms,status"
    )
    .map_err(|e| e.to_string())?;
    for name in FIXTURES {
        let p = load(name)?;
        let mut limits = std::collections::BTreeSet::from([0, 1, 2, 3, 8, 9, 10, 27, 28, 29, 100]);
        if boundaries {
            for x in 0..256 {
                let o = p.run(&[Bits::from_u64(8, x)], budget(&p, 4096))?;
                if o.code.low_u64() != 1 {
                    limits.insert(o.rows.saturating_sub(1));
                    limits.insert(o.rows);
                    limits.insert(o.rows + 1);
                }
            }
        }
        for steps in limits {
            let b = budget(&p, steps);
            for control in [false, true] {
                for style in 0..3 {
                    let t = Instant::now();
                    let compiled = match style {
                        0 => Compiled::baseline(&p, b, control)?,
                        1 => Compiled::optimized(&p, b, control)?,
                        _ => Compiled::optimized_compact(&p, b, control)?,
                    };
                    let cases = compiled.verify_truth(&p, b)?;
                    let mode = match style {
                        0 => "full_history",
                        1 => "residue_xor_inverse",
                        _ => "residue_inplace_inverse",
                    };
                    writeln!(
                        csv,
                        "{name},{steps},{mode},{control},{cases},{},{},pass",
                        compiled.checkpoints,
                        t.elapsed().as_millis()
                    )
                    .map_err(|e| e.to_string())?;
                }
            }
        }
        for steps in [16, 128] {
            let b = budget(&p, steps);
            let baseline = Compiled::optimized(&p, b, true)?;
            let (workspace, ladder, _) = baseline.auxiliary();
            let cap = baseline.external
                + workspace
                + ladder
                + 4 * baseline.state_width
                + 32 * baseline.residue_width;
            let t = Instant::now();
            let compiled = Compiled::pebbled_optimized(&p, b, true, cap)?;
            let cases = compiled.verify_truth(&p, b)?;
            writeln!(
                csv,
                "{name},{steps},regular_nested,true,{cases},{},{},pass",
                compiled.checkpoints,
                t.elapsed().as_millis()
            )
            .map_err(|e| e.to_string())?;
        }
        eprintln!("verified {name}");
    }
    Ok(())
}
