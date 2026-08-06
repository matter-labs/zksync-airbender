use std::fs::OpenOptions;
use std::io::Write;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::{lower_dag, validate};
use gpu_gkr_compiler::manual::{HELP, parse_args, search_config};
use gpu_gkr_compiler::{
    ForwardResourceProfile, ForwardSearchRequest, compile_forward, parse_forward_artifact,
    search_forward, validate_forward_artifact,
};

fn run(raw_args: Vec<String>) -> Result<(), String> {
    let args = parse_args(raw_args)?;
    if args.output.exists() && !args.replace {
        return Err(format!("{} exists; pass --replace", args.output.display()));
    }
    let layout_bytes = std::fs::read(&args.layout).map_err(|error| error.to_string())?;
    let layout: GKRCircuitArtifact<BabyBearField> =
        serde_json::from_slice(&layout_bytes).map_err(|error| error.to_string())?;
    let dag = lower_dag(&layout)?;
    validate(&dag)?;

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

    let config = search_config(&args);
    eprintln!(
        "search config: seed={} cache_buckets={} population={} evaluations={} {:?}",
        args.seed, args.cache_buckets, args.population, args.evaluations, config
    );
    let artifact = search_forward(ForwardSearchRequest {
        circuit: &args.circuit,
        dag: &dag,
        resources: ForwardResourceProfile {
            cache_buckets: args.cache_buckets,
        },
        config,
        seed: args.seed,
        incumbent: incumbent.as_ref(),
    })
    .map_err(|error| error.to_string())?;
    validate_forward_artifact(&dag, &artifact).map_err(|error| error.to_string())?;
    compile_forward(&dag, &artifact).map_err(|error| format!("{error:?}"))?;

    let bytes = serde_json::to_vec_pretty(&artifact).map_err(|error| error.to_string())?;
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
    validate_forward_artifact(&dag, &check).map_err(|error| error.to_string())?;
    compile_forward(&dag, &check).map_err(|error| format!("{error:?}"))?;
    std::fs::rename(&temporary, &args.output).map_err(|error| error.to_string())?;
    Ok(())
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
