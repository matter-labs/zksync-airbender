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
                                    if scratch_backed {
                                        "[scratch-prematerialized]"
                                    } else {
                                        ""
                                    }
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

/// Retained joint-matrix census guard (ISA-v2 spec §2 / §8, Task 3.7).
///
/// Independently of the `gkr_eval_isa` crate's `MatrixTable`, reproduce the §2
/// matrix-census figures from the LAUNCHER's own storage-layout model, so the
/// census stays honest against the launcher. Per layer, count the distinct
/// joint source+dst backings and assert the three ISA-cap invariants:
///   - ≤ 16 backings/layer (the 4-bit `MatrixSlot` / `GKR_MAX_SLOTS` cap),
///   - max column offset within the ISA cap (measured ≤ 645; the hard 10-bit
///     `col` cap is 1024, so 645+64 catches drift without false alarms),
///   - dual-write co-occurrence == 0 (no single dst address is produced by two
///     distinct producers — gate output or cache out — within one layer).
///
/// The backing key mirrors `gkr_eval_isa::compiler_v2::matrix_table::BackingKey`
/// (Task 2.1): `{ canonical_layer = address_storage_layer(addr), AddressClass =
/// classify(&addr, canonical_layer), field (FieldType), stride_class = 0 }`.
/// Critically, every field comes from the launcher's `GpuGKRStorageLayout`
/// (`layout.lookup`), NOT the ISA crate — the census is computed against the
/// model the launcher fills pointers against.
#[test]
#[serial]
fn retained_matrix_census_within_bounds() {
    use std::collections::{BTreeMap, BTreeSet};

    /// Joint backing key, mirroring `BackingKey` (Task 2.1). `stride_class` is
    /// always 0 (single-stride corpus, same as the ISA crate).
    #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct BackingKey {
        canonical_layer: usize,
        class: AddressClass,
        field: FieldType,
        stride_class: u8,
    }

    /// Per-address column offset within its backing; mirrors the ISA crate's
    /// `test_support::column_offset` (returns 0 for VirtualSetup, whose
    /// `offset()` panics).
    fn column_offset(addr: &GKRAddress) -> u32 {
        match addr {
            GKRAddress::VirtualSetup(_) => 0,
            other => other.offset() as u32,
        }
    }

    // ISA-cap headroom: the 10-bit `col` lane caps columns at 1024; the
    // measured corpus max is 645. Guard against silent drift well below the
    // hard cap but above the measured figure.
    const MEASURED_MAX_COL: u32 = 645;
    const COL_HEADROOM: u32 = 64;
    const HARD_COL_CAP: u32 = 1024;

    let dir = compiled_circuit_dir();
    let mut loaded = BTreeSet::new();
    let mut circuits_layers_exercised = 0usize;
    let mut global_max_backings = 0usize;
    let mut global_max_col = 0u32;

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

            // The launcher's OWN storage-layout model — the same data structure
            // every compact-`u16` descriptor builder consults.
            let layout = GpuGKRStorageLayout::from_artifact(&artifact);

            // Per artifact layer, gather the joint source+dst address set the
            // launcher would key into matrix slots, exactly as the launcher
            // enumerates a layer's gates and cache relations.
            for (layer_idx, layer) in artifact.layers.iter().enumerate() {
                // Distinct backing keys touched by this layer (source ∪ dst).
                let mut backings: BTreeSet<BackingKey> = BTreeSet::new();
                let mut max_col_this_layer = 0u32;
                // dst addresses and the distinct producers that write them, to
                // detect dual-write co-occurrence.
                let mut dst_producers: BTreeMap<GKRAddress, BTreeSet<String>> = BTreeMap::new();
                let mut had_any_addr = false;

                // Closure: resolve an address through the launcher layout into
                // its joint backing key, and fold it into the census.
                let mut record_addr =
                    |addr: GKRAddress, backings: &mut BTreeSet<BackingKey>, max_col: &mut u32| {
                        // VirtualSetup is aliased onto Setup at storage time and
                        // never claims its own backing (storage_layout drops it);
                        // skip to match the launcher.
                        if matches!(addr, GKRAddress::VirtualSetup(_)) {
                            return;
                        }
                        let canonical_layer = address_storage_layer(addr);
                        // Look the address up in the launcher's storage layout to
                        // get its (canonical_layer, class, field) — NOT recomputed
                        // from the ISA crate. `lookup` already applies the
                        // alias / same-address-canonical fallbacks the launcher
                        // uses, so CopyIn aliases resolve to their canonical.
                        let Some((clayer, class, field, _poly_idx)) =
                            layout.lookup(layer_idx, &addr)
                        else {
                            // Not every read resolves through a single layer's
                            // backing (e.g. setup polys keyed at layer 0 read by
                            // deeper layers resolve via the same-address
                            // canonical fallback inside `lookup`); if it truly
                            // has no backing, the address contributes no slot.
                            return;
                        };
                        backings.insert(BackingKey {
                            canonical_layer: clayer,
                            class,
                            field,
                            stride_class: 0,
                        });
                        // Sanity: the launcher's canonical layer must match the
                        // per-address storage layer for non-alias addresses.
                        debug_assert!(
                            clayer == canonical_layer || layout.aliases.contains_key(&addr),
                            "{addr:?} canonical layer {clayer} != address_storage_layer {canonical_layer}"
                        );
                        *max_col = (*max_col).max(column_offset(&addr));
                    };

                // 1. Gate sources (reads) and destinations (writes).
                for gate in layer
                    .gates
                    .iter()
                    .chain(layer.gates_with_external_connections.iter())
                {
                    let mut reads = Vec::new();
                    let mut writes = Vec::new();
                    collect_addresses_from_relation(
                        &gate.enforced_relation,
                        &mut reads,
                        &mut writes,
                    );
                    for addr in reads {
                        had_any_addr = true;
                        record_addr(addr, &mut backings, &mut max_col_this_layer);
                    }
                    for addr in &writes {
                        had_any_addr = true;
                        record_addr(*addr, &mut backings, &mut max_col_this_layer);
                        // CopyIn outputs are host-side view aliases (no kernel
                        // store); they don't claim a producer slot.
                        if layout.aliases.contains_key(addr) {
                            continue;
                        }
                        dst_producers
                            .entry(*addr)
                            .or_default()
                            .insert(format!("gate:{:?}", core::mem::discriminant(&gate.enforced_relation)));
                    }
                }

                // 2. Cache relations: reads + the cache addr itself as dst.
                for (cache_addr, cache_rel) in layer.cached_relations.iter() {
                    let mut reads = Vec::new();
                    collect_addresses_from_cache_relation(cache_rel, &mut reads);
                    for addr in reads {
                        had_any_addr = true;
                        record_addr(addr, &mut backings, &mut max_col_this_layer);
                    }
                    had_any_addr = true;
                    record_addr(*cache_addr, &mut backings, &mut max_col_this_layer);
                    dst_producers
                        .entry(*cache_addr)
                        .or_default()
                        .insert("cache".to_string());
                }

                if !had_any_addr {
                    continue;
                }
                circuits_layers_exercised += 1;

                // (a) ≤ 16 backings/layer.
                assert!(
                    backings.len() <= GKR_MAX_SLOTS,
                    "{tag} layer {layer_idx}: {} joint backings exceeds GKR_MAX_SLOTS={GKR_MAX_SLOTS}\nbackings={backings:?}",
                    backings.len(),
                );

                // (b) columns within the ISA cap.
                assert!(
                    max_col_this_layer < HARD_COL_CAP,
                    "{tag} layer {layer_idx}: max column offset {max_col_this_layer} \
                     exceeds the hard 10-bit col cap {HARD_COL_CAP}"
                );

                // (c) dual-write co-occurrence == 0: no dst address produced by
                // two distinct producers in the same layer.
                for (addr, producers) in dst_producers.iter() {
                    assert!(
                        producers.len() <= 1,
                        "{tag} layer {layer_idx}: dst {addr:?} dual-written by \
                         {} distinct producers {producers:?}",
                        producers.len(),
                    );
                }

                global_max_backings = global_max_backings.max(backings.len());
                global_max_col = global_max_col.max(max_col_this_layer);
            }
        }
    }

    // Non-vacuity: at least one layer exercised and backings actually counted.
    assert_compilable_circuits_loaded(&loaded);
    assert!(
        circuits_layers_exercised > 0,
        "census exercised no circuit×layer — fixtures missing or all empty"
    );
    assert!(
        global_max_backings > 0,
        "census counted zero backings — address enumeration produced nothing"
    );

    // §2 census figures, visible in test output.
    eprintln!(
        "[§2 retained census] circuits×layers exercised = {circuits_layers_exercised}, \
         per-layer max joint backings = {global_max_backings} (cap {GKR_MAX_SLOTS}), \
         max column offset = {global_max_col} (measured {MEASURED_MAX_COL}, hard cap {HARD_COL_CAP})"
    );
    // Drift guard: the measured corpus max column stays at/below the recorded
    // figure plus headroom. A jump far above 645 means a circuit changed shape
    // and the §2 figure needs re-confirming with RR before widening `col`.
    assert!(
        global_max_col <= MEASURED_MAX_COL + COL_HEADROOM,
        "max column offset {global_max_col} drifted far above the measured {MEASURED_MAX_COL} \
         (headroom {COL_HEADROOM}); re-confirm the §2 census figure before trusting the 10-bit col lane"
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
