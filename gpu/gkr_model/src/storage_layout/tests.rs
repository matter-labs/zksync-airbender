use super::*;
use serial_test::serial;
use std::path::PathBuf;

fn compiled_circuit_dir() -> PathBuf {
    // `gpu_gkr_model` lives at `gpu/gkr_model`; the compiled circuits are at the
    // workspace-root `cs/compiled_circuits` (two levels up, not one — the crate
    // moved under `gpu/` in the crate-stack reorg).
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("cs")
        .join("compiled_circuits")
}

fn load_artifact(
    json_path: &PathBuf,
) -> Option<GKRCircuitArtifact<field::baby_bear::base::BabyBearField>> {
    // The committed GKR layouts are serialized over BabyBear (the prover's base
    // field — see `circuit_prover`'s `GKRCircuitArtifact<BF>` and the
    // gkr_address_audit loader). Deserializing them under a different prime
    // field fails the coefficient range checks and yields `None` for every
    // circuit.
    let bytes = std::fs::read(json_path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

const CIRCUIT_BASENAMES: &[&str] = &[
    "add_sub_lui_auipc_mop",
    "bigint_with_extended_control",
    "blake2_g_function",
    "blake2_with_extended_control",
    "inits_and_teardowns_preprocessed",
    "jump_branch_slt",
    "keccak_special5",
    "mem_subword_only",
    "mem_word_only",
    "shift_binop",
    "unsigned_mul_div",
];

/// Circuits whose GKR artifact can be (re)compiled on this branch, so their
/// committed layout JSONs are current and deserialize. The remaining
/// `CIRCUIT_BASENAMES` are gated on in-progress compiler work — both
/// `compile_delegation_circuit` (`delegation_circuit.rs:41`, every delegation
/// circuit) and `no_field_gkr_max_quadratic_from_expr_and_constraint`
/// (`utils.rs:125`, the MaxQuad-from-expr circuits) are still `todo!()`, so
/// those layouts are stale (`missing field expression` / `structured_statements`)
/// and cannot be refreshed yet. The structural tests below verify every artifact
/// that loads and require at least these compilable ones to be present, so they
/// stay honest on this branch and automatically widen as the `todo!()`s land and
/// the stale layouts are regenerated.
const COMPILABLE_BASENAMES: &[&str] = &["add_sub_lui_auipc_mop", "jump_branch_slt"];

/// Asserts the set of basenames that successfully loaded covers at least every
/// currently-compilable circuit. Shared by the layout structural tests.
fn assert_compilable_circuits_loaded(loaded: &std::collections::BTreeSet<&str>) {
    for expected in COMPILABLE_BASENAMES {
        assert!(
            loaded.contains(expected),
            "compilable circuit {expected:?} failed to load — its layout JSON regressed \
             (loaded set: {loaded:?})"
        );
    }
}

/// Every `GKRAddress` produced by
/// `derive_dimension_reducing_inputs` for the artifact's
/// `global_output_map` must resolve through the layout when it is built
/// with `from_artifact_with_tower`. Per-tower-layer `log2_stride` halves
/// each round, all polys are ext-typed, and the class is always
/// `ThisLayerInnerLayerWrite` (since `addr.layer == output_layer`).
#[test]
#[serial]
fn tower_layout_covers_dim_reducing_outputs() {
    let dir = compiled_circuit_dir();
    let mut loaded = std::collections::BTreeSet::new();
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
            loaded.insert(*basename);

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
    assert_compilable_circuits_loaded(&loaded);
}

#[test]
#[serial]
fn layout_matches_audit_for_all_circuits() {
    let dir = compiled_circuit_dir();
    let mut loaded = std::collections::BTreeSet::new();
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
            loaded.insert(*basename);

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
    assert_compilable_circuits_loaded(&loaded);
}

#[test]
#[serial]
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
                    | R::LookupWithDensAndCachedSetup { .. }
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

/// The generated fused forward kernel for a main layer `L` writes its outputs
/// into at most four consolidated backings via the proxy ABI: `cache_base` /
/// `cache_ext` (this layer's `Cached{L,..}` writes, at storage layer `L`) and
/// `out_base` / `out_ext` (the next layer's `InnerLayer{L+1,..}` writes, at
/// storage layer `L+1`). For the no-scatter direct-write wiring to be correct
/// for ALL circuits, BOTH layouts, and ALL main layers, every address the
/// kernel stores must:
///   (1) resolve through the layout (have a backing),
///   (2) carry the field type the relation/cache produces,
///   (3) land in one of those four `(storage_layer, class, field)` slots,
///   (4) within each used slot, form a dense `poly_idx` range `0..count` that
///       is exactly the kernel's write-set (no foreign columns), and
///   (5) the layer's gate outputs target a single output layer `L+1`.
///
/// This is the structural precondition behind emitting `STORE_*` at the
/// layout's `poly_idx` and passing the consolidated backing base pointers
/// straight into the proxy. The test asserts (1)-(5) and prints a per-circuit
/// coverage summary (which of the four backings each circuit/layout/layer
/// uses, plus any escapes) so generality limits are visible, not silent.
#[test]
#[serial]
fn forward_kernel_outputs_fit_four_pointer_backing_model_all_main_layers() {
    use std::collections::BTreeSet;

    let dir = compiled_circuit_dir();
    let mut violations: Vec<String> = Vec::new();
    let mut summary = String::from("\n=== forward 4-pointer backing model coverage ===\n");
    let mut loaded = BTreeSet::new();

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
            loaded.insert(*basename);
            let tag = format!("{basename}/{}", if cached { "cached" } else { "no_caches" });
            let layout = GpuGKRStorageLayout::from_artifact(&artifact);

            // Which of the 4 model slots are used across this circuit/layout, and
            // any escaping (class, field) buckets (recorded with a sample reason).
            let mut used_slots: BTreeSet<(&'static str, &'static str)> = BTreeSet::new();
            let mut escapes: BTreeMap<String, usize> = BTreeMap::new();

            for (layer_idx, layer) in artifact.layers.iter().enumerate() {
                // 1. Kernel-stored forward outputs for this layer:
                //    caches (Cached{layer_idx,..}) + non-alias gate outputs.
                let mut outputs: Vec<(GKRAddress, FieldType)> = Vec::new();
                for (cache_addr, cache_rel) in layer.cached_relations.iter() {
                    outputs.push((*cache_addr, cache_relation_output_type(cache_rel)));
                }
                let mut gate_output_layers: BTreeSet<usize> = BTreeSet::new();
                for gate in layer
                    .gates
                    .iter()
                    .chain(layer.gates_with_external_connections.iter())
                {
                    for (addr, field) in relation_outputs(&gate.enforced_relation) {
                        // CopyIn aliases are host-side view aliases (no kernel store).
                        if layout.aliases.contains_key(&addr) {
                            continue;
                        }
                        match addr {
                            GKRAddress::InnerLayer { layer, .. }
                            | GKRAddress::Cached { layer, .. } => {
                                gate_output_layers.insert(layer);
                            }
                            _ => {}
                        }
                        outputs.push((addr, field));
                    }
                }
                // (5) single output layer for gate outputs.
                if gate_output_layers.len() > 1 {
                    violations.push(format!(
                        "{tag} layer {layer_idx}: gate outputs span output layers {gate_output_layers:?}"
                    ));
                }

                // 2. Bucket each output via the layout; classify into model vs escape.
                let mut kernel_polys: BTreeMap<(usize, AddressClass, FieldType), BTreeSet<u32>> =
                    BTreeMap::new();
                for (addr, field) in &outputs {
                    let sl = address_storage_layer(*addr);
                    match layout.lookup(sl, addr) {
                        None => violations.push(format!(
                            "{tag} layer {layer_idx}: forward output {addr:?} has no layout backing"
                        )),
                        Some((clayer, class, lfield, poly_idx)) => {
                            // (2) field consistency.
                            if lfield != *field {
                                violations.push(format!(
                                    "{tag} layer {layer_idx}: {addr:?} relation field {field:?} != layout field {lfield:?}"
                                ));
                            }
                            let is_cache_here =
                                clayer == layer_idx && class == AddressClass::ThisLayerCachedWrite;
                            let is_inner_next = clayer == layer_idx + 1
                                && class == AddressClass::ThisLayerInnerLayerWrite;
                            if is_cache_here || is_inner_next {
                                let slot_name = if is_cache_here { "cache" } else { "out" };
                                let field_name = match lfield {
                                    FieldType::Base => "base",
                                    FieldType::Ext => "ext",
                                };
                                used_slots.insert((slot_name, field_name));
                                kernel_polys
                                    .entry((clayer, class, lfield))
                                    .or_default()
                                    .insert(poly_idx);
                            } else {
                                // (3) escape: not one of the 4 model backings.
                                let scratch_backed =
                                    artifact.scratch_space_mapping.contains_key(addr);
                                let key = format!(
                                    "(L{clayer},{class:?},{lfield:?}){}",
                                    if scratch_backed { "[scratch-prematerialized]" } else { "" }
                                );
                                *escapes.entry(key).or_default() += 1;
                            }
                        }
                    }
                }

                // 4. For each used model backing: dense poly_idx 0..count, and the
                //    kernel write-set must equal the backing's full address set.
                for ((clayer, class, field), polys) in &kernel_polys {
                    let layer_layout = &layout.layers[*clayer];
                    let full: BTreeSet<u32> = layer_layout
                        .index
                        .iter()
                        .filter(|(_, (c, f, _))| c == class && f == field)
                        .map(|(_, (_, _, p))| *p)
                        .collect();
                    if &full != polys {
                        let foreign: Vec<u32> = full.difference(polys).copied().collect();
                        let extra: Vec<u32> = polys.difference(&full).copied().collect();
                        violations.push(format!(
                            "{tag} layer {layer_idx} backing (L{clayer},{class:?},{field:?}): kernel write-set != backing; foreign(in backing, not written)={foreign:?} extra(written, not in backing)={extra:?}"
                        ));
                    }
                    let count = layer_layout
                        .slot_poly_counts
                        .get(&StorageSlot {
                            class: *class,
                            field: *field,
                        })
                        .copied()
                        .unwrap_or(0);
                    let dense: BTreeSet<u32> = (0..count).collect();
                    if full != dense {
                        violations.push(format!(
                            "{tag} layer {layer_idx} backing (L{clayer},{class:?},{field:?}): poly_idx not dense 0..{count}; got {full:?}"
                        ));
                    }
                }
            }

            let slots_str = if used_slots.is_empty() {
                "(none)".to_string()
            } else {
                used_slots
                    .iter()
                    .map(|(s, f)| format!("{s}_{f}"))
                    .collect::<Vec<_>>()
                    .join(",")
            };
            let escapes_str = if escapes.is_empty() {
                "none".to_string()
            } else {
                escapes
                    .iter()
                    .map(|(k, n)| format!("{k}x{n}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            };
            summary.push_str(&format!(
                "  {tag:<40} layers={:<3} slots=[{slots_str}] escapes={escapes_str}\n",
                artifact.layers.len()
            ));
        }
    }

    println!("{summary}");
    assert_compilable_circuits_loaded(&loaded);
    assert!(
        violations.is_empty(),
        "4-pointer backing model violations ({}):\n{}",
        violations.len(),
        violations.join("\n")
    );
}

#[test]
#[serial]
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
