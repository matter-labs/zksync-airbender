use std::fs::OpenOptions;
use std::io::Write;
use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::lower_dag;
use gpu_gkr_compiler::{
    parse_forward_artifact, search_forward, ForwardSearchRequest, SearchConfig,
};

const HELP: &str = "gkr-forward-artifact \
  --circuit <stem> --layout <layout-json> --output <artifact-json> \
  --seed <u64> --cache-buckets <usize> --population <usize> --evaluations <usize> \
  [--incumbent <artifact-json>] [--replace]";

struct Args {
    circuit: String,
    layout: PathBuf,
    output: PathBuf,
    seed: u64,
    cache_buckets: usize,
    population: usize,
    evaluations: usize,
    incumbent: Option<PathBuf>,
    replace: bool,
}

fn next_value(raw: &mut impl Iterator<Item = String>, flag: &str) -> Result<String, String> {
    raw.next()
        .ok_or_else(|| format!("missing value for {flag}"))
}

fn parse_args(raw: impl IntoIterator<Item = String>) -> Result<Args, String> {
    let mut circuit = None;
    let mut layout = None;
    let mut output = None;
    let mut seed = None;
    let mut cache_buckets = None;
    let mut population = None;
    let mut evaluations = None;
    let mut incumbent = None;
    let mut replace = false;
    let mut raw = raw.into_iter();
    while let Some(flag) = raw.next() {
        match flag.as_str() {
            "--circuit" => circuit = Some(next_value(&mut raw, &flag)?),
            "--layout" => layout = Some(PathBuf::from(next_value(&mut raw, &flag)?)),
            "--output" => output = Some(PathBuf::from(next_value(&mut raw, &flag)?)),
            "--seed" => {
                seed = Some(
                    next_value(&mut raw, &flag)?
                        .parse()
                        .map_err(|_| "invalid --seed")?,
                )
            }
            "--cache-buckets" => {
                cache_buckets = Some(
                    next_value(&mut raw, &flag)?
                        .parse()
                        .map_err(|_| "invalid --cache-buckets")?,
                )
            }
            "--population" => {
                population = Some(
                    next_value(&mut raw, &flag)?
                        .parse()
                        .map_err(|_| "invalid --population")?,
                )
            }
            "--evaluations" => {
                evaluations = Some(
                    next_value(&mut raw, &flag)?
                        .parse()
                        .map_err(|_| "invalid --evaluations")?,
                )
            }
            "--incumbent" => incumbent = Some(PathBuf::from(next_value(&mut raw, &flag)?)),
            "--replace" => replace = true,
            other => return Err(format!("unknown argument {other}\n{HELP}")),
        }
    }
    let args = Args {
        circuit: circuit.ok_or("missing --circuit")?,
        layout: layout.ok_or("missing --layout")?,
        output: output.ok_or("missing --output")?,
        seed: seed.ok_or("missing --seed")?,
        cache_buckets: cache_buckets.ok_or("missing --cache-buckets")?,
        population: population.ok_or("missing --population")?,
        evaluations: evaluations.ok_or("missing --evaluations")?,
        incumbent,
        replace,
    };
    let expected = format!("{}_schedule_b{}_gkr.json", args.circuit, args.cache_buckets);
    if args.output.file_name().and_then(|name| name.to_str()) != Some(&expected) {
        return Err(format!("output must end in {expected}"));
    }
    Ok(args)
}

fn run(raw_args: Vec<String>) -> Result<(), String> {
    let args = parse_args(raw_args)?;
    if args.output.exists() && !args.replace {
        return Err(format!("{} exists; pass --replace", args.output.display()));
    }
    let layout_bytes = std::fs::read(&args.layout).map_err(|error| error.to_string())?;
    let layout: GKRCircuitArtifact<BabyBearField> =
        serde_json::from_slice(&layout_bytes).map_err(|error| error.to_string())?;
    let dag = lower_dag(&layout)?;

    let incumbent_bytes = args
        .incumbent
        .as_ref()
        .map(|path| std::fs::read(path).map_err(|error| error.to_string()))
        .transpose()?;
    let incumbent = incumbent_bytes
        .as_deref()
        .map(|bytes| parse_forward_artifact(bytes, "incumbent"))
        .transpose()
        .map_err(|error| error.to_string())?;

    let config = SearchConfig {
        population: args.population,
        evaluations: args.evaluations,
        ..SearchConfig::production()
    };
    eprintln!(
        "search config: seed={} cache_buckets={} population={} evaluations={} {:?}",
        args.seed, args.cache_buckets, args.population, args.evaluations, config
    );
    let artifact = search_forward(ForwardSearchRequest {
        circuit: &args.circuit,
        dag: &dag,
        cache_buckets: args.cache_buckets,
        config,
        seed: args.seed,
        incumbent: incumbent.as_ref(),
    })
    .map_err(|error| error.to_string())?;

    let bytes = serde_json::to_vec(&artifact).map_err(|error| error.to_string())?;
    let temporary = args
        .output
        .with_extension(format!("json.tmp.{}", std::process::id()));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .map_err(|error| error.to_string())?;
    file.write_all(&bytes).map_err(|error| error.to_string())?;
    file.write_all(b"\n").map_err(|error| error.to_string())?;
    drop(file);
    let check = std::fs::read(&temporary).map_err(|error| error.to_string())?;
    let check =
        parse_forward_artifact(&check, "temporary output").map_err(|error| error.to_string())?;
    if check.circuit != args.circuit || check.budget_buckets != args.cache_buckets {
        return Err("temporary artifact metadata does not match the command".into());
    }
    std::fs::rename(&temporary, &args.output).map_err(|error| error.to_string())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args() -> Vec<String> {
        "--circuit tiny --layout tiny.json --output tiny_schedule_b4_gkr.json --seed 7 \
         --cache-buckets 4 --population 2 --evaluations 8"
            .split_whitespace()
            .map(str::to_owned)
            .collect()
    }

    #[test]
    fn output_name_is_exact() {
        let mut args = args();
        let output = args.iter().position(|arg| arg == "--output").unwrap() + 1;
        args[output] = "another.json".into();
        assert!(parse_args(args).is_err());
    }
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        println!("{HELP}");
        return;
    }
    if let Err(error) = run(args) {
        eprintln!("{error}\n{HELP}");
        std::process::exit(2);
    }
}
