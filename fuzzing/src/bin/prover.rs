use std::process::ExitCode;

#[cfg(feature = "prover")]
mod imp {
    use std::process::ExitCode;

    use clap::Parser;
    use fuzzing::prover::run;
    use fuzzing::prover::Cli;
    use fuzzing::setup_logging;

    pub fn main() -> ExitCode {
        setup_logging();
        let cli = Cli::parse();
        match run(cli) {
            Ok(_) => {
                println!("Command finished!");
                ExitCode::SUCCESS
            }
            Err(err) => {
                eprintln!("Fuzzer encountered a fatal error: {err}");
                ExitCode::FAILURE
            }
        }
    }
}

fn main() -> ExitCode {
    #[cfg(feature = "prover")]
    return imp::main();

    #[cfg_attr(feature = "prover", allow(unreachable_code))]
    {
        eprintln!("Enable this tool by enabling the 'prover' feature at compile time");
        ExitCode::FAILURE
    }
}
