use risc_v_simulator::{runner::run_simple_simulator, sim::SimulatorConfig};

pub fn main() {
    // let args: Vec<String> = std::env::args().collect();
    // dbg!(&args);
    // assert_eq!(args.len(), 2);
    // let path = &args[1];
    println!("ZK RISC-V simulator is starting");

    let path = "../zksync-os/zksync_os/app.bin";
    let path_sym = "../zksync-os/zksync_os/app.elf";

    use risc_v_simulator::sim::DiagnosticsConfig;
    use risc_v_simulator::sim::ProfilerConfig;

    let mut config = SimulatorConfig::simple(path);
    config.entry_point = 0;
    config.diagnostics = Some({
        let mut d = DiagnosticsConfig::new(std::path::PathBuf::from(path_sym));

        d.profiler_config = {
            let mut p =
                ProfilerConfig::new(std::env::current_dir().unwrap().join("flamegraph.svg"));

            p.frequency_recip = 1;
            p.reverse_graph = false;

            Some(p)
        };

        d
    });

    let output = run_simple_simulator(config);
    dbg!(output);
}
