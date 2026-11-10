# Pebble executable model

Rust 2024, standard library only, no external dependencies. Run inside this directory:

```sh
cargo test --offline
cargo run --release --offline
cargo run --release --offline -- --verify-boundaries
python3 report.py
```

The last command is an optional standard-library formatter for `RESULTS.md`; Rust does not depend on Python. The default run generates the full measurement grid, exact-vs-nested chain study, and a shorter whole-oracle verification grid. The boundary command checks N−1, N, N+1 for every observed halt/fault count over all 8-bit inputs.

See [RESULTS.md](RESULTS.md) for verified domains, CORE corrections, measured/computed distinctions, and remaining limits. Machine results are under `results/`.

Other commands:

```sh
cargo run --release --offline -- --one collatz 1000000000 10000
cargo run --release --offline -- --hierarchy collatz 1000000000 10000
cargo run --release --offline -- --emit inc8 3
```

`--emit` streams native permutation gates: `mcx controls... -> target`, plus LIFO `alloc base count` / `free base count`. It can produce enormous output. `--hierarchy` writes a finite shared description: numbered gate/seq/call/adj/ctrl/rep/with definitions; arrays are wire maps, and repetition shifts list nonzero `(wire,delta)` pairs. Definition IDs refer to earlier records. Its first line gives the external wire count and root definition.

Library entry points are `Program::parse`, `Program::bind_classical`, `Program::run`, `Machine::build`, and `Compiled::{baseline,optimized,optimized_compact,best}`. Fixed classical ptr/f64 arguments are supplied as bit patterns and never counted as quantum inputs. The parser does not authenticate object metadata. Unlisted instructions, lifted memory, and full lproc forwarding interfaces are unsupported explicitly.
