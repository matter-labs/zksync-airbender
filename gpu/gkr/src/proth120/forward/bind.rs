use super::challenge_banks::ForwardChallengeBanks;
use super::desc::*;
use super::lower::{lower_desc, FwdVmInputs, LoweredFwdVm, ResolvedColumn};
use super::setup::GpuGKRForwardSetupPr;
use crate::forward::{
    LoweredSlotInitialInput, LoweredSlotOutput, PreparedDimensionReductionForward,
};
use crate::gkr_address_audit::AddressClass;
use crate::proth120::inputs::Proth120GkrWitnessInputs;
use crate::proth120::programs::GkrProgramsPr;
use crate::storage_layout::FieldType;
use crate::upstream::{GKRAddress, GKRRelationPr as GKRRelation, PR};
use crate::{GpuBaseFieldPoly, GpuGKRStorage};
use era_cudart::result::CudaResult;
use gpu_core::primitives::device_structures::DeviceMatrixImpl;
use gpu_prover_context::ProverContext;
use std::ptr::null_mut;
use std::sync::Arc;

pub(crate) fn resolve_storage_column(
    storage: &GpuGKRStorage<PR, PR>,
    addr: GKRAddress,
) -> Option<ResolvedColumn> {
    if let Some(poly) = storage.try_get_base_poly(addr) {
        return Some(ResolvedColumn {
            is_e4: false,
            ptr: poly.as_ptr().cast(),
            matrix_base: poly.backing.as_ptr() as *mut u8,
            stride_bytes: u32::try_from(poly.len * size_of::<PR>())
                .expect("Proth120 base stride exceeds u32"),
        });
    }
    storage.try_get_ext_poly(addr).map(|poly| ResolvedColumn {
        is_e4: true,
        ptr: poly.as_ptr().cast(),
        matrix_base: poly.backing.as_ptr() as *mut u8,
        stride_bytes: u32::try_from(poly.len * size_of::<PR>())
            .expect("Proth120 extension stride exceeds u32"),
    })
}

pub(crate) fn prepare_vm(
    programs: &GkrProgramsPr,
    storage: &mut GpuGKRStorage<PR, PR>,
    witness: &Proth120GkrWitnessInputs<'_>,
    setup: &GpuGKRForwardSetupPr,
    banks: &ForwardChallengeBanks,
    top_bits: &[u32],
    context: &ProverContext,
) -> CudaResult<LoweredFwdVm> {
    let circuit = &programs.runtime_circuit;
    let rows = circuit.trace_len;
    for (layer_idx, layer) in circuit.layers.iter().enumerate() {
        for (&scratch_idx, &address) in &circuit.scratch_space_mapping_rev {
            if matches!(address, GKRAddress::InnerLayer { layer, .. } if layer == layer_idx)
                && storage.try_get_base_poly(address).is_none()
            {
                storage.insert_base_field_at_layer(
                    layer_idx,
                    address,
                    GpuBaseFieldPoly::from_arc(
                        Arc::clone(&witness.scratch),
                        scratch_idx * rows,
                        rows,
                    ),
                );
            }
        }
        for (storage_layer, class) in [
            (layer_idx, AddressClass::ThisLayerCachedWrite),
            (layer_idx + 1, AddressClass::ThisLayerInnerLayerWrite),
        ] {
            let outputs: Vec<_> = programs
                .storage_layout
                .layers
                .get(storage_layer)
                .into_iter()
                .flat_map(|l| l.index.iter())
                .filter(|(_, (c, _, _))| *c == class)
                .map(|(address, (_, field, _))| (*address, *field))
                .collect();
            for (address, field) in outputs {
                match field {
                    FieldType::Base => {
                        let view = storage.allocate_base_view(storage_layer, address, context)?;
                        storage.insert_base_field_at_layer(storage_layer, address, view);
                    }
                    FieldType::Ext => {
                        let view = storage.allocate_ext_view(storage_layer, address, context)?;
                        storage.insert_extension_at_layer(storage_layer, address, view);
                    }
                }
            }
        }
        for gate in layer
            .gates
            .iter()
            .chain(&layer.gates_with_external_connections)
        {
            match &gate.enforced_relation {
                GKRRelation::CopyInBaseField { input, output } => {
                    let source = storage
                        .try_get_base_poly(*input)
                        .expect("Proth120 base copy source is missing")
                        .clone_shared();
                    storage.insert_base_field_at_layer(layer_idx + 1, *output, source);
                }
                GKRRelation::CopyInExtensionField { input, output } => {
                    let source = storage.get_ext_poly(*input).clone_shared();
                    storage.insert_extension_at_layer(layer_idx + 1, *output, source);
                }
                _ => {}
            }
        }
    }
    let header = FwdVmInputs {
        mapping_arena: [
            witness.generic_lookup_mapping.as_ptr(),
            witness.range_check_16_lookup_mapping.as_ptr(),
            witness.range_check_timestamp_lookup_mapping.as_ptr(),
        ],
        decoder_mapping_col: (!witness.decoder_lookup_mapping.is_empty()).then_some(0),
        decoder_mapping: witness.decoder_lookup_mapping.as_ptr(),
        table: setup.generic_lookup.as_ptr(),
        table_len: setup.generic_lookup.len() as u32,
        count: u32::try_from(rows).expect("Proth120 forward rows exceed u32"),
        inits_and_teardowns_top_bits: top_bits,
    };
    let mut lowered = lower_desc(&programs.forward.layers, &header, &|address| {
        resolve_storage_column(storage, address)
    })
    .unwrap_or_else(|e| panic!("Proth120 forward VM lowering failed: {e:?}"));
    assert_eq!(
        lowered.lookup_additive_slot, programs.challenge_plan.lookup_additive_slot,
        "Proth120 lookup bank slot mismatch"
    );
    assert_eq!(
        lowered.decoder_fill_slot, programs.challenge_plan.decoder_fill_slot,
        "Proth120 decoder bank slot mismatch"
    );
    lowered.desc.arg_derived = banks.arg_derived.as_ptr();
    lowered.desc.const_derived = banks.const_derived.as_ptr();
    Ok(lowered)
}

pub(crate) fn schedule_vm(
    lowered: &mut LoweredFwdVm,
    prepared: &PreparedDimensionReductionForward<PR>,
    context: &ProverContext,
) -> CudaResult<u32> {
    let fused = lowered.desc.count.is_multiple_of(128)
        && prepared.total_rounds >= FUSED_REDUCTION_ROUNDS as u32;
    if fused {
        bind_fused_reduction_prefix(&mut lowered.desc, prepared);
    } else {
        lowered.desc.reduction_pair_count = 0;
    }
    super::kernels::launch_vm(&lowered.desc, context)?;
    Ok(if fused {
        FUSED_REDUCTION_ROUNDS as u32
    } else {
        0
    })
}
fn bind_fused_reduction_prefix(
    desc: &mut FwdVmDesc,
    prepared: &PreparedDimensionReductionForward<PR>,
) {
    assert!(desc.count > 0 && desc.count.is_multiple_of(128));
    assert_eq!(desc.count.trailing_zeros(), prepared.initial_trace_log_2);
    assert_eq!(
        prepared.per_round_slot_outputs.len(),
        prepared.total_rounds as usize
    );
    assert_eq!(
        prepared.slot_initial_inputs.len(),
        prepared.slot_output_types.len()
    );
    assert!(!prepared.slot_initial_inputs.is_empty());
    assert!(
        prepared
            .slot_output_types
            .windows(2)
            .all(|pair| pair[0] <= pair[1]),
        "reduction slots must follow OutputType order"
    );
    for outputs in &prepared.per_round_slot_outputs {
        assert_eq!(outputs.len(), prepared.slot_initial_inputs.len());
    }

    let mut slot = 0usize;
    let mut pair = 0usize;
    while slot < prepared.slot_output_types.len() {
        assert!(pair < REDUCTION_PAIR_CAP);
        let output_type = prepared.slot_output_types[slot];
        let range_end = prepared.slot_output_types[slot..]
            .iter()
            .position(|kind| *kind != output_type)
            .map(|offset| slot + offset)
            .unwrap_or(prepared.slot_output_types.len());
        let arity = range_end - slot;
        let record = match output_type {
            crate::upstream::OutputType::PermutationProduct
            | crate::upstream::OutputType::InitsAndTeardownsProduct => {
                assert_eq!(arity, 2);
                let input = [slot, slot + 1].map(|slot| {
                    let LoweredSlotInitialInput::PairwiseProduct { input } =
                        prepared.slot_initial_inputs[slot]
                    else {
                        panic!("pairwise reduction input changed kind")
                    };
                    assert!(!input.is_null());
                    input
                });
                let mut round_outputs = [[null_mut(); 2]; FUSED_REDUCTION_ROUNDS];
                for (round, outputs) in round_outputs.iter_mut().enumerate() {
                    for (output, slot) in outputs.iter_mut().zip([slot, slot + 1]) {
                        let LoweredSlotOutput::PairwiseProduct { output: pointer } =
                            prepared.per_round_slot_outputs[round][slot]
                        else {
                            panic!("pairwise reduction output changed kind")
                        };
                        assert!(!pointer.is_null());
                        *output = pointer;
                    }
                }
                FwdVmReductionPair {
                    input,
                    round_outputs,
                    kind: REDUCTION_PAIR_PAIRWISE2,
                    reserved: 0,
                }
            }
            crate::upstream::OutputType::Lookup16Bits
            | crate::upstream::OutputType::LookupTimestamps
            | crate::upstream::OutputType::GenericLookup => {
                assert_eq!(arity, 1);
                let LoweredSlotInitialInput::LookupPair { num, den } =
                    prepared.slot_initial_inputs[slot]
                else {
                    panic!("lookup reduction input changed kind")
                };
                assert!(!num.is_null() && !den.is_null());
                let mut round_outputs = [[null_mut(); 2]; FUSED_REDUCTION_ROUNDS];
                for (round, outputs) in round_outputs.iter_mut().enumerate() {
                    let LoweredSlotOutput::LookupPair {
                        output_num,
                        output_den,
                    } = prepared.per_round_slot_outputs[round][slot]
                    else {
                        panic!("lookup reduction output changed kind")
                    };
                    assert!(!output_num.is_null() && !output_den.is_null());
                    *outputs = [output_num, output_den];
                }
                FwdVmReductionPair {
                    input: [num, den],
                    round_outputs,
                    kind: REDUCTION_PAIR_LOOKUP,
                    reserved: 0,
                }
            }
        };
        desc.reduction_pairs[pair] = record;
        pair += 1;
        slot = range_end;
    }
    desc.reduction_pair_count = pair as u32;
}
