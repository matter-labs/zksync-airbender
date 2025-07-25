use super::*;

use cs::one_row_compiler::CompiledCircuitArtifact;
use prover::prover_stages::Proof;
use risc_v_simulator::abstractions::non_determinism::QuasiUARTSourceState;
use risc_v_simulator::cycle::IMIsaConfigWithAllDelegations;
use std::collections::VecDeque;
use verifier_common::proof_flattener::flatten_proof_for_skeleton;
use verifier_common::proof_flattener::flatten_query;

pub fn profile_inner(
    config: &ProfilingConfig,
    circuit_dir: &str,
    proofs_dir: &str,
    compiled_verifiers_dir: &str,
    flamegraph_dir: &str,
) {
    let proof: Proof =
        deserialize_from_file(&format!("{}/{}", proofs_dir, config.proof_file_name()));
    let compiled_circuit: CompiledCircuitArtifact<Mersenne31Field> =
        deserialize_from_file(&format!("{}/{}", circuit_dir, config.layout_file_name()));

    let mut oracle_data: Vec<u32> = vec![];
    {
        oracle_data.extend(flatten_proof_for_skeleton(
            &proof,
            compiled_circuit
                .memory_layout
                .shuffle_ram_inits_and_teardowns
                .is_some(),
        ));
        for query in proof.queries.iter() {
            oracle_data.extend(flatten_query(query));
        }

        let path = format!("{}/{}", compiled_verifiers_dir, config.bin_file_name());
        let path_sym = format!("{}/{}", compiled_verifiers_dir, config.elf_file_name());
        let flamegraph_path = format!("{}/{}", flamegraph_dir, config.flamegraph_file_name());

        use risc_v_simulator::runner::run_simple_with_entry_point_and_non_determimism_source_for_config;
        use risc_v_simulator::sim::*;

        let mut config = SimulatorConfig::simple(path);
        config.cycles = 1 << 23;
        config.entry_point = 0;
        config.diagnostics = Some({
            let mut d = DiagnosticsConfig::new(std::path::PathBuf::from(path_sym));

            d.profiler_config = {
                let mut p =
                    ProfilerConfig::new(std::env::current_dir().unwrap().join(flamegraph_path));

                p.frequency_recip = 1;
                p.reverse_graph = false;

                Some(p)
            };

            d
        });

        let inner = VecDeque::<u32>::from(oracle_data);
        let oracle = VectorBasedNonDeterminismSource(inner, QuasiUARTSourceState::Ready);
        let (_, output) = run_simple_with_entry_point_and_non_determimism_source_for_config::<
            _,
            // IWithoutByteAccessIsaConfigWithDelegation,
            IMIsaConfigWithAllDelegations,
        >(config, oracle);
        dbg!(output);
    }
}

struct VectorBasedNonDeterminismSource(VecDeque<u32>, QuasiUARTSourceState);

impl
    risc_v_simulator::abstractions::non_determinism::NonDeterminismCSRSource<
        risc_v_simulator::abstractions::memory::VectorMemoryImpl,
    > for VectorBasedNonDeterminismSource
{
    fn read(&mut self) -> u32 {
        self.0.pop_front().unwrap()
    }
    fn write_with_memory_access(
        &mut self,
        _memory: &risc_v_simulator::abstractions::memory::VectorMemoryImpl,
        value: u32,
    ) {
        self.1.process_write(value);
    }
}
