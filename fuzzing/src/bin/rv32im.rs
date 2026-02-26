use clap::Parser;
use fuzzing::rv32im::run;
use fuzzing::rv32im::Mode;
use fuzzing::setup_logging;

#[derive(Parser)]
struct Cli {
    #[arg(long)]
    mode: Mode,
    #[arg(long)]
    test_one: bool,
}

fn main() {
    setup_logging();
    let cli = Cli::parse();
    run(cli.mode, cli.test_one);
}
