use clap::Parser;
use fuzzing::setup_logging;
use fuzzing::witgen::checks::Checks;
use fuzzing::witgen::run;
use fuzzing::witgen::targets::Circuits;

#[derive(Parser)]
struct Cli {
    #[arg(long)]
    circuit: Circuits,
    #[arg(long)]
    check: Checks,
    #[arg(long, default_value_t = 1)]
    samples: usize,
}

fn main() {
    setup_logging();
    let cli = Cli::parse();
    run(cli.circuit, cli.check, cli.samples);
}
