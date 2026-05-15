use super::*;
use std::path::PathBuf;

fn compiled_circuit_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("cs")
        .join("compiled_circuits")
}

fn load_artifact(json_path: &PathBuf) -> Option<GKRCircuitArtifact<field::Mersenne31Field>> {
    let bytes = std::fs::read(json_path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

const CIRCUIT_BASENAMES: &[&str] = &[
    "add_sub_lui_auipc_mop_preprocessed",
    "bigint_with_extended_control",
    "blake2_with_extended_control",
    "inits_and_teardowns_preprocessed",
    "jump_branch_slt_preprocessed",
    "keccak_special5",
    "mem_subword_only_preprocessed",
    "mem_word_only_preprocessed",
    "shift_binop_preprocessed",
    "unsigned_mul_div_preprocessed",
];

/// Every `GKRAddress` produced by
/// `derive_dimension_reducing_inputs` for the artifact's
/// `global_output_map` must resolve through the layout when it is built
/// with `from_artifact_with_tower`. Per-tower-layer `log2_stride` halves
/// each round, all polys are ext-typed, and the class is always
/// `ThisLayerInnerLayerWrite` (since `addr.layer == output_layer`).
#[test]
fn tower_layout_covers_dim_reducing_outputs() {
    let dir = compiled_circuit_dir();
    let mut covered = 0;
    for basename in CIRCUIT_BASENAMES {
        for cached in [true, false] {
            let suffix = if cached {
                "_layout_gkr.json"
            } else {
                "_layout_no_caches_gkr.json"
            };
            let path = dir.join(format!("{basename}{suffix}"));
            let Some(artifact) = load_artifact(&path) else {
                continue;
            };
            covered += 1;

            // Pick a final_trace_log_2 of 0 to maximize tower depth (matches
            // the prover's typical configuration). For circuits with very
            // small trace_len we still get at least one tower round.
            let initial_trace_log_2 = artifact.trace_len.trailing_zeros() as usize;
            if initial_trace_log_2 == 0 {
                continue;
            }
            let final_trace_log_2 = 0usize;
            let layout =
                GpuGKRStorageLayout::from_artifact_with_tower(&artifact, final_trace_log_2);

            // Re-derive the tower address sequence via the same logic the
            // forward pass uses, then assert each address resolves with the
            // expected `(class, field, poly_idx)` and per-layer log2_stride.
            let initial_layer_idx = artifact.layers.len();
            let total_rounds = initial_trace_log_2 - final_trace_log_2;
            let mut layer_inputs = artifact.global_output_map.clone();
            let mut current_layer_idx = initial_layer_idx;
            for round in 0..total_rounds {
                let output_layer = current_layer_idx + 1;
                let expected_log2_stride = (initial_trace_log_2 - 1 - round) as u32;
                let layer_layout = layout.layers.get(output_layer).unwrap_or_else(|| {
                    panic!("layout missing tower layer {output_layer} for {basename}/{cached}")
                });
                assert_eq!(
                        layer_layout.log2_stride, expected_log2_stride,
                        "tower layer {output_layer} log2_stride mismatch (basename={basename}, cached={cached})",
                    );

                let mut output_idx: u32 = 0;
                let mut next_inputs = BTreeMap::new();
                for (arg_type, inputs) in layer_inputs.iter() {
                    assert_eq!(inputs.len(), 2);
                    let out_a = GKRAddress::InnerLayer {
                        layer: output_layer,
                        offset: output_idx as usize,
                    };
                    let pa = output_idx;
                    output_idx += 1;
                    let out_b = GKRAddress::InnerLayer {
                        layer: output_layer,
                        offset: output_idx as usize,
                    };
                    let pb = output_idx;
                    output_idx += 1;

                    let (class_a, field_a, poly_idx_a) =
                        layer_layout.lookup(&out_a).unwrap_or_else(|| {
                            panic!("tower layer {output_layer} layout missing {out_a:?}")
                        });
                    assert_eq!(class_a, AddressClass::ThisLayerInnerLayerWrite);
                    assert_eq!(field_a, FieldType::Ext);
                    assert_eq!(poly_idx_a, pa);
                    let (class_b, field_b, poly_idx_b) =
                        layer_layout.lookup(&out_b).unwrap_or_else(|| {
                            panic!("tower layer {output_layer} layout missing {out_b:?}")
                        });
                    assert_eq!(class_b, AddressClass::ThisLayerInnerLayerWrite);
                    assert_eq!(field_b, FieldType::Ext);
                    assert_eq!(poly_idx_b, pb);

                    next_inputs.insert(*arg_type, vec![out_a, out_b]);
                }
                layer_inputs = next_inputs;
                current_layer_idx += 1;
            }
        }
    }
    assert!(covered >= CIRCUIT_BASENAMES.len());
}

#[test]
fn layout_matches_audit_for_all_circuits() {
    let dir = compiled_circuit_dir();
    let mut covered = 0;
    for basename in CIRCUIT_BASENAMES {
        for cached in [true, false] {
            let suffix = if cached {
                "_layout_gkr.json"
            } else {
                "_layout_no_caches_gkr.json"
            };
            let path = dir.join(format!("{basename}{suffix}"));
            let Some(artifact) = load_artifact(&path) else {
                continue;
            };
            covered += 1;

            let layout = GpuGKRStorageLayout::from_artifact(&artifact);
            // The layout may extend beyond `artifact.layers.len()` when
            // gates at the last artifact layer write into a deeper
            // storage layer (the dim-reducing tower above the main
            // layers). The layout always covers at least every artifact
            // layer.
            assert!(
                    layout.layers.len() >= artifact.layers.len(),
                    "layout coverage must include every artifact layer (basename={basename}, cached={cached})"
                );
            assert_eq!(layout.trace_len, artifact.trace_len);

            // Within each layer, every (slot, FieldType) entry's poly
            // count must match the BTreeSet of distinct addresses that
            // resolve to it via `index`.
            for (layer_idx, layer_layout) in layout.layers.iter().enumerate() {
                let mut expected: BTreeMap<StorageSlot, u32> = BTreeMap::new();
                for (_, (class, field, poly_idx)) in layer_layout.index.iter() {
                    let entry = expected
                        .entry(StorageSlot {
                            class: *class,
                            field: *field,
                        })
                        .or_default();
                    *entry = (*entry).max(*poly_idx + 1);
                }
                for (slot, count) in layer_layout.slot_poly_counts.iter() {
                    let exp = expected.get(slot).copied().unwrap_or(0);
                    assert!(
                            *count >= exp,
                            "layer {layer_idx}: slot_poly_counts[{slot:?}] = {count} < highest poly_idx+1 = {exp} (basename={basename}, cached={cached})"
                        );
                }
            }
        }
    }
    assert!(
        covered >= CIRCUIT_BASENAMES.len(),
        "expected at least one mode per basename to load; covered={covered}"
    );
}

#[test]
fn no_caches_artifacts_use_only_gpu_forward_supported_variants() {
    use cs::gkr_compiler::NoFieldGKRRelation as R;

    let dir = compiled_circuit_dir();
    let mut covered = 0;
    for basename in CIRCUIT_BASENAMES {
        let path = dir.join(format!("{basename}_layout_no_caches_gkr.json"));
        let Some(artifact) = load_artifact(&path) else {
            continue;
        };
        covered += 1;
        for (layer_idx, layer) in artifact.layers.iter().enumerate() {
            for gate in layer
                .gates
                .iter()
                .chain(layer.gates_with_external_connections.iter())
            {
                match &gate.enforced_relation {
                    R::CopyInBaseField { .. }
                    | R::CopyInExtensionField { .. }
                    | R::LinearBaseFieldRelation { .. }
                    | R::EnforceSingleMaxQuadraticConstraint { .. }
                    | R::InitialGrandProductFromCaches { .. }
                    | R::InitialGrandProductWithoutCaches { .. }
                    | R::MaterializeGrandProductTermExpression { .. }
                    | R::TrivialProduct { .. }
                    | R::MaskIntoIdentityProduct { .. }
                    | R::MaterializeSingleLookupInput { .. }
                    | R::MaterializedVectorLookupInput { .. }
                    | R::LookupWithCachedDensAndSetup { .. }
                    | R::LookupWithDensAndSetupExpressions { .. }
                    | R::LookupPairFromBaseInputs { .. }
                    | R::LookupPairFromMaterializedBaseInputs { .. }
                    | R::LookupFromMaterializedBaseInputWithSetup { .. }
                    | R::LookupUnbalancedPairWithMaterializedBaseInputs { .. }
                    | R::LookupPairFromVectorInputs { .. }
                    | R::LookupPairFromMaterializedVectorInputs { .. }
                    | R::LookupPairFromCachedVectorInputs { .. }
                    | R::LookupFromVectorInputWithSetup { .. }
                    | R::LookupFromMaterializedVectorInputWithSetup { .. }
                    | R::LookupUnbalancedPairWithVectorInputs { .. }
                    | R::LookupUnbalancedPairWithMaterializedVectorInputs { .. }
                    | R::AggregateLookupRationalPair { .. }
                    | R::InitsOrTeardownsInitialPair { .. } => {}
                    R::MaxQuadratic { output, .. } => {
                        // Backward dispatch (build_main_layer_kernel_blueprints_static)
                        // supports MaxQuadratic unconditionally. The forward path still
                        // expects the output to be pre-materialized via scratch_space_mapping;
                        // without it the unimplemented! arm in forward.rs fires.
                        assert!(
                                artifact.scratch_space_mapping.contains_key(output),
                                "{basename} layer {layer_idx}: non-scratch-backed MaxQuadratic output {output:?} requires direct GPU forward support"
                            );
                    }
                    R::EnforceConstraintsMaxQuadratic { .. }
                    | R::UnbalancedGrandProductWithCache { .. } => {
                        panic!(
                                "{basename} layer {layer_idx}: no-cache artifact uses unsupported GPU forward relation {:?}",
                                gate.enforced_relation
                            );
                    }
                }
            }
        }
    }
    assert!(covered > 0, "expected at least one no-cache artifact");
}

/// Builds a small hand-crafted layout: layer 0 holds 2 base polys (slot
/// `ThisLayerInnerLayerWrite`) + 2 ext polys (slot `ThisLayerCachedWrite`),
/// trace_len 4. Used by `consolidated_views_share_backing_and_offset` to
/// exercise the consolidated allocator without a real circuit artifact.
fn handcrafted_layout(
    base_addr_a: GKRAddress,
    base_addr_b: GKRAddress,
    ext_addr_a: GKRAddress,
    ext_addr_b: GKRAddress,
) -> GpuGKRStorageLayout {
    let trace_len = 4usize;
    let log2_stride = trace_len.trailing_zeros();
    let mut index = BTreeMap::new();
    index.insert(
        base_addr_a,
        (
            AddressClass::ThisLayerInnerLayerWrite,
            FieldType::Base,
            0u32,
        ),
    );
    index.insert(
        base_addr_b,
        (
            AddressClass::ThisLayerInnerLayerWrite,
            FieldType::Base,
            1u32,
        ),
    );
    index.insert(
        ext_addr_a,
        (AddressClass::ThisLayerCachedWrite, FieldType::Ext, 0u32),
    );
    index.insert(
        ext_addr_b,
        (AddressClass::ThisLayerCachedWrite, FieldType::Ext, 1u32),
    );
    let mut slot_poly_counts = BTreeMap::new();
    slot_poly_counts.insert(
        StorageSlot {
            class: AddressClass::ThisLayerInnerLayerWrite,
            field: FieldType::Base,
        },
        2u32,
    );
    slot_poly_counts.insert(
        StorageSlot {
            class: AddressClass::ThisLayerCachedWrite,
            field: FieldType::Ext,
        },
        2u32,
    );
    GpuGKRStorageLayout {
        trace_len,
        artifact_log2_stride: log2_stride,
        layers: vec![GpuGKRLayerLayout {
            index,
            slot_poly_counts,
            log2_stride,
        }],
        aliases: BTreeMap::new(),
    }
}

#[test]
#[serial_test::serial]
fn consolidated_views_share_backing_and_offset() {
    use crate::prover::gkr::GpuGKRStorage;
    use crate::prover::test_utils::make_test_context;
    use cs::definitions::GKRAddress;
    use field::{Mersenne31Field as BF, Mersenne31Quartic as E4};
    use std::sync::Arc;

    let context = make_test_context(64, 1);

    let base_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let base_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let ext_a = GKRAddress::Cached {
        layer: 0,
        offset: 0,
    };
    let ext_b = GKRAddress::Cached {
        layer: 0,
        offset: 1,
    };
    let layout = Arc::new(handcrafted_layout(base_a, base_b, ext_a, ext_b));

    let mut storage: GpuGKRStorage<BF, E4> = GpuGKRStorage::default();
    storage.set_layout(Arc::clone(&layout));

    // Two base views on the same class share backing; offsets differ by
    // exactly `trace_len` elements.
    let view_a = storage.allocate_base_view(0, base_a, &context).unwrap();
    let view_b = storage.allocate_base_view(0, base_b, &context).unwrap();
    assert!(view_a.shares_backing_with(&view_b));
    assert_eq!(view_a.offset(), 0);
    assert_eq!(view_b.offset(), layout.trace_len);
    assert_eq!(view_a.len(), layout.trace_len);
    assert_eq!(view_b.len(), layout.trace_len);
    unsafe {
        assert_eq!(view_a.as_ptr().add(layout.trace_len), view_b.as_ptr());
    }
    // `as_mut_ptr()` reports the same address as `as_ptr()`.
    assert_eq!(view_a.as_ptr() as *mut BF, view_a.as_mut_ptr());
    assert_eq!(view_b.as_ptr() as *mut BF, view_b.as_mut_ptr());

    // Two ext views on the same class share their (separate) backing.
    let ext_view_a = storage.allocate_ext_view(0, ext_a, &context).unwrap();
    let ext_view_b = storage.allocate_ext_view(0, ext_b, &context).unwrap();
    assert!(ext_view_a.shares_backing_with(&ext_view_b));
    assert_eq!(ext_view_a.offset(), 0);
    assert_eq!(ext_view_b.offset(), layout.trace_len);
    unsafe {
        assert_eq!(
            ext_view_a.as_ptr().add(layout.trace_len),
            ext_view_b.as_ptr()
        );
    }

    // Repeat allocations for the same address return views into the same
    // backing (caller is responsible for not aliasing writes; this is
    // the same property that lets gpu_prover keep pointers alive across
    // descriptor builds).
    let view_a_again = storage.allocate_base_view(0, base_a, &context).unwrap();
    assert!(view_a.shares_backing_with(&view_a_again));
    assert_eq!(view_a.offset(), view_a_again.offset());
}

#[test]
#[serial_test::serial]
fn allocate_base_view_panics_when_address_is_ext_typed() {
    use crate::prover::gkr::GpuGKRStorage;
    use crate::prover::test_utils::make_test_context;
    use cs::definitions::GKRAddress;
    use field::{Mersenne31Field as BF, Mersenne31Quartic as E4};
    use std::sync::Arc;

    let context = make_test_context(64, 1);
    let base_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let base_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let ext_a = GKRAddress::Cached {
        layer: 0,
        offset: 0,
    };
    let ext_b = GKRAddress::Cached {
        layer: 0,
        offset: 1,
    };
    let layout = Arc::new(handcrafted_layout(base_a, base_b, ext_a, ext_b));

    let mut storage: GpuGKRStorage<BF, E4> = GpuGKRStorage::default();
    storage.set_layout(layout);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        storage.allocate_base_view(0, ext_a, &context).unwrap()
    }));
    assert!(
        result.is_err(),
        "allocate_base_view must panic when called with an ext-typed address"
    );
}

#[test]
fn relation_outputs_classifies_known_variants() {
    // Spot-check the classification table against the dispatch in
    // forward.rs that distinguishes base vs ext insertion sites.
    use cs::definitions::gkr::NoFieldLinearRelation;
    use cs::definitions::GKRAddress::*;
    use cs::gkr_compiler::NoFieldGKRRelation::*;

    let dummy_addr = InnerLayer {
        layer: 1,
        offset: 0,
    };
    let dummy_input = NoFieldLinearRelation {
        constant: 0,
        linear_terms: vec![].into_boxed_slice(),
    };

    let base = LinearBaseFieldRelation {
        input: dummy_input.clone(),
        output: dummy_addr,
    };
    assert_eq!(relation_outputs(&base), vec![(dummy_addr, FieldType::Base)]);

    let ext = CopyInExtensionField {
        input: dummy_addr,
        output: dummy_addr,
    };
    assert_eq!(relation_outputs(&ext), vec![(dummy_addr, FieldType::Ext)]);
}
