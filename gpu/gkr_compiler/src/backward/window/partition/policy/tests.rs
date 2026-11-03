use super::*;
use crate::backward::common::Bf;
use crate::backward::{compile_r0, corpus_tests::CORPUS};

fn hardware() -> R0PartitionHardware {
    R0PartitionHardware {
        sm_count: 100,
        l2_bytes: 64 << 20,
        clock_hz: 2e9,
        memory_bytes_per_second: 1e12,
        issue_slots_per_sm_cycle: 4.0,
        original_blocks_per_sm: 3,
        grid_blocks_per_sm: 3,
    }
}

#[test]
fn cpu_partition_selection_uses_current_device_geometry() {
    let directory =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let mut selected_split = false;
    for name in CORPUS {
        let artifact: cs::gkr_compiler::GKRCircuitArtifact<Bf> =
            serde_json::from_slice(&std::fs::read(directory.join(name)).unwrap()).unwrap();
        let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
        for program in compile_r0(&dag).unwrap() {
            let candidates = program.partition_candidates;
            let rows = (artifact.trace_len >> 3).div_ceil(32).max(1);
            for device in [
                hardware(),
                R0PartitionHardware {
                    sm_count: 1,
                    ..hardware()
                },
                R0PartitionHardware {
                    l2_bytes: 0,
                    ..hardware()
                },
                R0PartitionHardware {
                    l2_bytes: usize::MAX,
                    ..hardware()
                },
                R0PartitionHardware {
                    memory_bytes_per_second: 1e20,
                    ..hardware()
                },
            ] {
                let plan = candidates.select(rows, &device).unwrap();
                assert!(candidates.plans.iter().any(|p| std::ptr::eq(p, plan)));
                assert_eq!(
                    plan.source_bytes_per_tile.iter().sum::<usize>(),
                    candidates.total_bytes_per_tile
                );
                if device.l2_bytes == 0
                    || device.l2_bytes == usize::MAX
                    || device.memory_bytes_per_second == 1e20
                {
                    assert_eq!(plan.parts.len(), 1);
                }
            }
            let memory_bound = R0PartitionHardware {
                l2_bytes: 1,
                memory_bytes_per_second: 1.0,
                ..hardware()
            };
            selected_split |= candidates.select(rows, &memory_bound).unwrap().parts.len() > 1;
            assert!(candidates.select(0, &hardware()).is_err());
            for invalid in [
                R0PartitionHardware {
                    sm_count: 0,
                    ..hardware()
                },
                R0PartitionHardware {
                    clock_hz: f64::NAN,
                    ..hardware()
                },
                R0PartitionHardware {
                    memory_bytes_per_second: 0.0,
                    ..hardware()
                },
                R0PartitionHardware {
                    grid_blocks_per_sm: 0,
                    ..hardware()
                },
            ] {
                assert!(candidates.select(rows, &invalid).is_err());
            }
        }
    }
    assert!(selected_split);
}
