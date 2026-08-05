use std::path::PathBuf;

use crate::{CrossoverKind, SearchConfig};

pub const HELP: &str = "gkr-forward-artifact \
  --circuit <stem> --layout <layout-json> --output <artifact-json> \
  --seed <u64> --cache-cells <usize> --population <usize> --evaluations <usize> \
  [--incumbent <artifact-json>] [--replace]";

#[derive(Debug, PartialEq, Eq)]
pub struct ManualArgs {
    pub circuit: String,
    pub layout: PathBuf,
    pub output: PathBuf,
    pub seed: u64,
    pub cache_cells: usize,
    pub population: usize,
    pub evaluations: usize,
    pub incumbent: Option<PathBuf>,
    pub replace: bool,
}

pub fn parse_args<I>(args: I) -> Result<ManualArgs, String>
where
    I: IntoIterator<Item = String>,
{
    let mut circuit = None;
    let mut layout = None;
    let mut output = None;
    let mut seed = None;
    let mut cache_cells = None;
    let mut population = None;
    let mut evaluations = None;
    let mut incumbent = None;
    let mut replace = false;
    let mut args = args.into_iter();
    while let Some(flag) = args.next() {
        let value = |args: &mut I::IntoIter, flag: &str| {
            args.next()
                .ok_or_else(|| format!("missing value for {flag}"))
        };
        match flag.as_str() {
            "--circuit" => circuit = Some(value(&mut args, &flag)?),
            "--layout" => layout = Some(PathBuf::from(value(&mut args, &flag)?)),
            "--output" => output = Some(PathBuf::from(value(&mut args, &flag)?)),
            "--seed" => {
                seed = Some(
                    value(&mut args, &flag)?
                        .parse()
                        .map_err(|_| "invalid --seed")?,
                )
            }
            "--cache-cells" => {
                cache_cells = Some(
                    value(&mut args, &flag)?
                        .parse()
                        .map_err(|_| "invalid --cache-cells")?,
                )
            }
            "--population" => {
                population = Some(
                    value(&mut args, &flag)?
                        .parse()
                        .map_err(|_| "invalid --population")?,
                )
            }
            "--evaluations" => {
                evaluations = Some(
                    value(&mut args, &flag)?
                        .parse()
                        .map_err(|_| "invalid --evaluations")?,
                )
            }
            "--incumbent" => incumbent = Some(PathBuf::from(value(&mut args, &flag)?)),
            "--replace" => replace = true,
            "--help" | "-h" => return Err(HELP.to_owned()),
            other => return Err(format!("unknown argument {other}\n{HELP}")),
        }
    }
    let args = ManualArgs {
        circuit: circuit.ok_or("missing --circuit")?,
        layout: layout.ok_or("missing --layout")?,
        output: output.ok_or("missing --output")?,
        seed: seed.ok_or("missing --seed")?,
        cache_cells: cache_cells.ok_or("missing --cache-cells")?,
        population: population.ok_or("missing --population")?,
        evaluations: evaluations.ok_or("missing --evaluations")?,
        incumbent,
        replace,
    };
    let expected = format!("{}_schedule_b{}_gkr.json", args.circuit, args.cache_cells);
    if args.output.file_name().and_then(|name| name.to_str()) != Some(&expected) {
        return Err(format!("output must end in {expected}"));
    }
    Ok(args)
}

pub fn search_config(args: &ManualArgs) -> SearchConfig {
    SearchConfig {
        population: args.population,
        evaluations: args.evaluations,
        crossover: CrossoverKind::Order,
        ..SearchConfig::production()
    }
}
