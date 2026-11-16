use gpu_core::primitives::field::{BF, E4};

use crate::{forward::vm::lower_common::*, upstream::PrimeField};

impl LoweringField for BF {
    type Ext = E4;
    const NEEDS_SETUP_FILL: bool = true;
    const SEPARATE_DECODER_MAPPING: bool = false;
    fn canonical_constant(value: u128) -> Self {
        let canonical = u32::try_from(value)
            .ok()
            .filter(|&v| v < BF::CHARACTERISTICS_U32)
            .unwrap_or_else(|| {
                panic!("forward constant {value} is not a canonical BabyBear value")
            });
        BF::from_u32_with_reduction(canonical)
    }
    fn inits_top_bits(raw: u32, shift: u32) -> Self {
        BF::from_u32_with_reduction(raw.checked_shl(shift).unwrap_or(0))
    }
}

#[cfg(test)]
mod tests {
    use crate::forward::vm::lower_common::{append_program, empty_desc, resolve_test_columns};
    use crate::{
        baby_bear::GkrPrograms,
        upstream::{GKRAddress, GKRCircuitArtifact},
    };
    use gpu_core::primitives::field::{BF, E4};
    use gpu_gkr_compiler::{
        ForwardDstLine as DstLine, ForwardInstr as Instr, ForwardOperandField as OperandField,
        ForwardOperandLine as OperandLine, ForwardProgram as Program,
    };
    use gpu_trace::witness::circuit_type::{
        CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
        UnrolledNonMemoryCircuitType,
    };
    use std::{path::Path, sync::Arc};
    #[test]
    fn cpu_encoded_programs_concatenate_and_record_layer_boundaries() {
        let first = Program {
            instrs: vec![Instr::Mov {
                dir: gpu_gkr_compiler::ForwardMovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Smem { cell: 1 }),
            }],
        };
        let second = Program {
            instrs: vec![
                Instr::Mov {
                    dir: gpu_gkr_compiler::ForwardMovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Smem { cell: 2 }),
                },
                Instr::Mov {
                    dir: gpu_gkr_compiler::ForwardMovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 3 }),
                    src: None,
                },
            ],
        };
        let mut desc = empty_desc::<BF, E4>();
        let mut next_lane = 0;

        append_program(&mut desc, &mut next_lane, 0, &first);
        append_program(&mut desc, &mut next_lane, 1, &second);

        assert_eq!(desc.layers[0].program_offset, 0);
        assert_eq!(desc.layers[0].instruction_count, 1);
        assert_eq!(desc.layers[1].program_offset, 2);
        assert_eq!(desc.layers[1].instruction_count, 2);
        assert_eq!(next_lane, 6);
        assert_eq!(&desc.program[..6], &[3, 5, 3, 9, 7, 6]);
    }

    fn lower_embedded_circuit(layout: &str, circuit_type: CircuitType) {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits")
            .join(layout);
        let artifact: GKRCircuitArtifact<BF> =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let programs = GkrPrograms::compile(circuit_type, Arc::new(artifact)).unwrap();
        crate::baby_bear::forward::recompute_plan::check_recompute_bindings(&programs);

        let resolved = resolve_test_columns(&programs.forward.layers, 64);
        let resolve = |address: GKRAddress| {
            resolved
                .iter()
                .find_map(|(candidate, column)| (*candidate == address).then_some(*column))
        };
        let header = crate::baby_bear::forward::vm::lower::FwdVmInputs {
            mapping_arena: [
                std::ptr::without_provenance(1),
                std::ptr::without_provenance(2),
                std::ptr::without_provenance(3),
            ],
            decoder_mapping_col: Some(0),
            table: std::ptr::without_provenance(4),
            table_len: 16,
            count: 16,
            inits_and_teardowns_top_bits: &[0; 32],
        };

        crate::baby_bear::forward::vm::lower::lower_desc(
            &programs.forward.layers,
            &header,
            &resolve,
            &|_| unsafe { core::mem::zeroed() },
        );
    }

    #[test]
    fn cpu_all_embedded_forward_circuits_fit_one_descriptor() {
        use DelegationCircuitType::*;
        use UnrolledCircuitType::*;
        use UnrolledMemoryCircuitType::*;
        use UnrolledNonMemoryCircuitType::*;

        let cases = [
            (
                "add_sub_lui_auipc_mop_layout_gkr.json",
                CircuitType::Unrolled(NonMemory(AddSubLuiAuipcMop)),
            ),
            (
                "jump_branch_slt_layout_gkr.json",
                CircuitType::Unrolled(NonMemory(JumpBranchSlt)),
            ),
            (
                "unsigned_mul_div_layout_gkr.json",
                CircuitType::Unrolled(NonMemory(MulDivUnsigned)),
            ),
            (
                "shift_binop_layout_gkr.json",
                CircuitType::Unrolled(NonMemory(ShiftBinary)),
            ),
            (
                "mem_word_only_layout_gkr.json",
                CircuitType::Unrolled(Memory(LoadStoreWordOnly)),
            ),
            (
                "mem_subword_only_layout_gkr.json",
                CircuitType::Unrolled(Memory(LoadStoreSubwordOnly)),
            ),
            (
                "inits_and_teardowns_layout_gkr.json",
                CircuitType::Unrolled(InitsAndTeardowns),
            ),
            (
                "unified_reduced_machine_layout_gkr.json",
                CircuitType::Unrolled(Unified),
            ),
            (
                "bigint_with_extended_control_layout_gkr.json",
                CircuitType::Delegation(BigIntWithControl),
            ),
            (
                "keccak_special5_layout_gkr.json",
                CircuitType::Delegation(KeccakSpecial5),
            ),
            (
                "blake2_with_extended_control_layout_gkr.json",
                CircuitType::Delegation(Blake2WithCompression),
            ),
            (
                "blake2_g_function_layout_gkr.json",
                CircuitType::Delegation(Blake2GFunction),
            ),
        ];

        for (layout, circuit_type) in cases {
            lower_embedded_circuit(layout, circuit_type);
        }
    }
}
