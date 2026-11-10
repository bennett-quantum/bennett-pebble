use pebble_model::{circuit, compiler::Compiled, measure};
fn parse_cap(arg: Option<&String>) -> Result<Option<usize>, String> {
    match arg.map(String::as_str) {
        None | Some("unlimited") => Ok(None),
        Some(s) => Ok(Some(s.parse().map_err(|_| "invalid peak budget")?)),
    }
}
fn run() -> Result<(), String> {
    let args: Vec<_> = std::env::args().collect();
    match args.get(1).map(String::as_str){
        Some("--one")=>{
            let name=args.get(2).ok_or("fixture missing")?;
            let b=args.get(3).ok_or("B missing")?.parse().map_err(|_|"invalid B")?;
            println!("{}",measure::one(name,b,parse_cap(args.get(4))?)?);
        }
        Some("--verify")=>measure::verification(false)?,
        Some("--verify-boundaries")=>measure::verification(true)?,
        Some("--measure")=>measure::measurements()?,
        Some("--chain")=>measure::chain_study()?,
        Some("--emit"|"--hierarchy")=>{
            let name=args.get(2).ok_or("fixture missing")?;
            let p=measure::load(name)?;
            let b=args.get(3).ok_or("B missing")?.parse().map_err(|_|"invalid B")?;
            let compiled=Compiled::best(&p,measure::budget(&p,b),true,parse_cap(args.get(4))?)?;
            let output=std::io::stdout().lock();
            if args[1]=="--hierarchy"{circuit::emit_hierarchy(&compiled.term,compiled.external,output)}else{circuit::emit(&compiled.term,compiled.external,output)}.map_err(|e|e.to_string())?;
        }
        None=>{
            measure::measurements()?;measure::chain_study()?;measure::verification(false)?;
            println!("Wrote results/measurements.json, tradeoff.csv, chain.csv, chain.json, verification.csv. See RESULTS.md for scope and limitations.");
        }
        _=>return Err("usage: cargo run --release -- [--verify | --verify-boundaries | --measure | --chain | --one FIXTURE B [PEAK|unlimited] | --emit FIXTURE B [PEAK|unlimited] | --hierarchy FIXTURE B [PEAK|unlimited]]".into())
    }
    Ok(())
}
fn main() {
    if let Err(e) = run() {
        eprintln!("{e}");
        std::process::exit(1);
    }
}
