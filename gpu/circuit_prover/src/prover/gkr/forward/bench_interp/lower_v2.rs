//! CPU→GPU lowering of a `gkr_eval_isa::compiler_v2` compiled forward program
//! (`CompiledForward2`) into the v2 `interp_desc2` ABI
//! (`native/bench/gkr_fwd_interp_v2.cu`, mirrored by `interp_v2_gpu::InterpDesc2`).
//!
//! This is the REAL-WITNESS binding (Phase 5.2): unlike the staged parity test
//! (`tests_v2.rs`), which uploads random source columns, this builds an
//! `InterpDesc2` whose matrix-slot columns / gather tables / challenge banks all
//! point at the PRODUCTION buffers a `CircuitFixture` materialized during its
//! capturing forward pass. The kernel then reads exactly what the flat forward
//! launchers read, so its `Dst::Materialize` outputs can be compared bit-exactly
//! against the production FLAT golden resident in `fixture.storage`.
//!
//! Test/bench-only (the module is `cfg(all(test, feature = "bench"))`), so
//! `gkr_eval_isa` is a dev-dependency and the upstream-import rules are relaxed.

use std::collections::BTreeMap;
use std::ptr;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::stage1::GpuGKRStage1Output;
use crate::prover::ProverContext;

use cs::definitions::{GKRAddress, TableType, VirtualSetupPoly};
use cs::gkr_compiler::codegen_ir::{CacheKind, CodegenLayer, Domain};
use field::{Field, FieldExtension, PrimeField};

use gkr_eval_isa::compiler_v2::gather::GatherDescriptor;
use gkr_eval_isa::compiler_v2::CompiledForward2;
use gkr_eval_isa::isa_v2::{Dst, Header, IndirectKind, LdcSub, Operand, RoutineId};
use gkr_eval_isa::test_support::{collect_v2_address_refs, column_offset};

use super::fixture::{
    materialize_virtual_setup_column, resolve_addr, CircuitFixture, CircuitKeepalive, LayerFixture,
};
use super::interp_v2_gpu::InterpDesc2;

/// alloc + H2D a host slice; returns the device buffer (kept alive by caller).
/// Mirrors the `upload` helper in `tests_v2.rs` (test/bench-only synchronous H2D).
pub(super) fn upload<X: Copy>(context: &ProverContext, host: &[X]) -> DeviceAllocation<X> {
    let mut dev: DeviceAllocation<X> = context
        .alloc(host.len().max(1), AllocationPlacement::Top)
        .unwrap();
    if !host.is_empty() {
        memory_copy_async(&mut dev[0..host.len()], host, context.get_exec_stream()).unwrap();
    }
    dev
}

/// One materialized output column the kernel writes: its matrix slot/col, the
/// fresh device buffer the kernel stores into, its e4-ness, and the PRODUCTION
/// golden address (`storage_column(addr)` resident in `fixture.storage`) to
/// compare against after the launch.
#[cfg(not(no_cuda))]
pub(super) struct OutColumn {
    pub slot: u8,
    pub col: u16,
    pub e4: bool,
    /// The (slot,col) -> address inverse from `collect_v2_address_refs`; its
    /// resident production column is the bit-exact golden.
    pub golden_addr: GKRAddress,
    /// Fresh device buffer (E4-backed; bf columns use the low 4 bytes of each
    /// element). Kept alive here so the readback pointer stays valid.
    pub buf: DeviceAllocation<E4>,
}

/// Everything the launched `InterpDesc2` borrows raw pointers into. Holding it
/// keeps every device allocation alive across launch + readback (mirrors v1
/// `InterpDeviceSetup`). The `out_columns` field carries the per-output compare
/// metadata the parity test reads back.
#[cfg(not(no_cuda))]
pub(super) struct InterpDesc2Setup {
    pub desc: InterpDesc2,
    /// Materialize outputs to read back + compare against production goldens.
    pub out_columns: Vec<OutColumn>,
    /// Number of matrix slots (== matrix_table.len()).
    pub n_matrix_slots: usize,
    /// Program lane count (for logging / non-vacuity).
    pub n_lanes: usize,
    /// Count of gather descriptors that could NOT be bound to a real production
    /// table (e.g. launcher-deferred InitsTeardownsHighAddr): logged by the test.
    pub unbound_gathers: Vec<String>,

    // --- keepalives: every device allocation the desc points into ---
    _lanes_dev: DeviceAllocation<u16>,
    _consts_dev: DeviceAllocation<BF>,
    _cc_dev: DeviceAllocation<E4>,
    _scalars_dev: DeviceAllocation<E4>,
    _col_base_dev: DeviceAllocation<u32>,
    _columns_dev: DeviceAllocation<u64>,
    _out_base_dev: DeviceAllocation<u32>,
    _out_cols_dev: DeviceAllocation<u64>,
    _virtual_src: Vec<DeviceAllocation<BF>>,
    /// Materialized virtual-setup `n` tables for MappedVirtualBf gathers (base).
    _gather_bf_bufs: Vec<DeviceAllocation<BF>>,
    /// Launcher-deferred 1-element scalar buffers (InitsTeardownsHighAddr).
    _inits_td_bufs: Vec<DeviceAllocation<E4>>,
    _desc_kind_dev: DeviceAllocation<u8>,
    _desc_n_dev: DeviceAllocation<u64>,
    _desc_mapping_dev: DeviceAllocation<u64>,
    _desc_n_len_dev: DeviceAllocation<u32>,
    _desc_mask_dev: DeviceAllocation<u64>,
    _desc_fill_alpha_dev: DeviceAllocation<u32>,
    _desc_table_id_dev: DeviceAllocation<u32>,
    _err_dev: DeviceAllocation<u32>,
}

/// Read the `&stage1` of a fixture's keepalive (the lookup-mapping device tables
/// are bound there, exactly as the flat cache launchers source them).
#[cfg(not(no_cuda))]
fn fixture_stage1(fixture: &CircuitFixture) -> &GpuGKRStage1Output {
    match &fixture.keepalive {
        CircuitKeepalive::Unrolled { stage1, .. } => stage1,
        CircuitKeepalive::Delegation(keepalive) => &keepalive.stage1,
    }
}

/// Build the v2 interpreter device side for one real-fixture (circuit, layer)
/// point: invert the matrix table to columns/col_base, bind sources to resident
/// production storage, materialize virtual-setup source columns, allocate fresh
/// materialize-output buffers, bind every gather to its production cache table,
/// stage the challenge banks, and assemble the `InterpDesc2`. Sized for the full
/// `fixture.trace_len`. The returned setup owns every allocation so the desc's
/// raw pointers stay valid through launch + readback.
#[cfg(not(no_cuda))]
pub(super) fn build_interp_desc2_real(
    fixture: &CircuitFixture,
    layer_idx: usize,
    cf2: &CompiledForward2,
    cg_layer: &CodegenLayer,
) -> InterpDesc2Setup {
    let context = fixture.context();
    let layer = &fixture.layers[layer_idx];
    let t = fixture.trace_len;
    let mt = &cf2.matrix_table;
    let n_slots = mt.len();

    // ----- (slot,col) -> addr inverse + per-slot max column from the SAME
    // field-annotated walk the matrix table was built from. -----
    // inv[(slot,col)] = addr (the table dedups addr -> one slot, and a given
    // (slot,col) maps to one addr; collisions would be a table bug).
    let mut inv: BTreeMap<(u8, u16), GKRAddress> = BTreeMap::new();
    let mut max_col_for_slot = vec![0u16; n_slots];
    for (addr, _dom) in collect_v2_address_refs(cg_layer) {
        // VirtualSetup columns are GATHER-ONLY: they are read via the
        // MappedVirtualBf gather's `desc_n` value table, never as an
        // `Operand::Affine` matrix column. They collide with `Setup` at
        // (slot, col=0) because `column_offset` returns 0 for both and
        // `classify()` maps both `Setup(_)` and `VirtualSetup(_)` to
        // `AddressClass::Setup` (one backing slot). Excluding them from the READ
        // table makes the real `Setup` source win DETERMINISTICALLY, independent
        // of the `collect_v2_address_refs` walk order; the VirtualSetup datum is
        // bound separately by `bind_mapped_virtual`. (Probe over the stage-3 L0
        // corpus: (slot 3, col 0) is the ONLY collision and it IS Affine-read, so
        // last-writer-wins here would be a latent mis-bind.)
        if matches!(addr, GKRAddress::VirtualSetup(_)) {
            continue;
        }
        let slot = mt
            .slot_for(&addr)
            .expect("collect_v2_address_refs address must have a backing slot");
        let col = mt.column_of(&addr);
        inv.insert((slot, col), addr);
        if col >= max_col_for_slot[slot as usize] {
            max_col_for_slot[slot as usize] = col;
        }
    }

    // col_base: prefix sum over slots of (max col + 1). Length n_slots + 1.
    let mut col_base = vec![0u32; n_slots + 1];
    for s in 0..n_slots {
        // capacity of slot s = max col seen + 1 (0 if the slot is never columned,
        // but a slot only exists because some addr resolved to it, so >= 1).
        col_base[s + 1] = col_base[s] + (max_col_for_slot[s] as u32 + 1);
    }
    let total_cols = col_base[n_slots] as usize;

    // slot_is_e4 bitset.
    let mut slot_is_e4: u32 = 0;
    for s in 0..n_slots {
        if mt.field_is_ext(s as u8) {
            slot_is_e4 |= 1 << s;
        }
    }

    // ----- Source columns table (READ side). For each (slot,col)->addr that is a
    // production-resident READABLE source, place its device base. Virtual-setup
    // base columns have NO resident buffer; materialize them. Entries never read
    // (e.g. materialize-only destinations) stay null. -----
    let mut columns_host = vec![0u64; total_cols];
    // `inv` excludes VirtualSetup (gather-only, bound via `desc_n`), so every
    // entry here is a resident production source resolved through storage.
    let virtual_src: Vec<DeviceAllocation<BF>> = Vec::new();
    for (&(slot, col), &addr) in &inv {
        let flat_idx = col_base[slot as usize] as usize + col as usize;
        if let Some(p) = resolve_addr(layer, &fixture.storage, addr) {
            columns_host[flat_idx] = p as u64;
        }
        // else: not resident as a readable source — likely a materialize-only
        // destination. Left null; the kernel only errors if it is actually read.
    }

    // ----- Materialize outputs table (WRITE side). Enumerate every distinct
    // `Dst::Materialize { slot, col }` in the program; allocate a fresh device
    // buffer per output and place its ptr at out_columns[out_base[slot]+col].
    // out_base parallels col_base sizing (re-uses the same per-slot column caps,
    // so out_columns and columns share index geometry). -----
    let mut materialize_set: BTreeMap<(u8, u16), bool> = BTreeMap::new(); // (slot,col)->e4
    for ins in &cf2.program.instrs {
        for d in &ins.dsts {
            if let Dst::Materialize { slot, col } = d {
                materialize_set
                    .entry((*slot, *col))
                    .or_insert_with(|| mt.field_is_ext(*slot));
            }
        }
    }
    let out_base = col_base.clone();
    let mut out_cols_host = vec![0u64; total_cols];
    let mut out_columns: Vec<OutColumn> = Vec::new();
    let mut out_is_e4: u32 = 0;
    for (&(slot, col), &e4) in &materialize_set {
        let golden_addr = *inv.get(&(slot, col)).unwrap_or_else(|| {
            panic!(
                "materialize (slot {slot}, col {col}) has no (slot,col)->addr inverse \
                 (every Materialize backs a collected address)"
            )
        });
        // Fresh zero-init buffer; bf columns use the low limb of each E4 element.
        let buf = upload(context, &vec![E4::ZERO; t]);
        let flat_idx = out_base[slot as usize] as usize + col as usize;
        out_cols_host[flat_idx] = buf.as_ptr() as u64;
        if e4 {
            out_is_e4 |= 1 << slot;
        }
        out_columns.push(OutColumn {
            slot,
            col,
            e4,
            golden_addr,
            buf,
        });
    }

    // ----- Constant banks. -----
    // consts: Montgomery bf (the kernel reads raw bf; the CPU stores canonical).
    let consts_mont: Vec<BF> = cf2
        .program
        .consts
        .iter()
        .map(|&c| BF::from_u32_with_reduction(c))
        .collect();
    let consts_dev = upload(context, &consts_mont);

    // challenge_scalars e4[8]: [0] gamma, [1+role] perm_challenges, [7] perm_additive.
    let ch = fixture.bench_challenges();
    let mut scalars = [E4::ZERO; 8];
    scalars[0] = ch.gamma;
    for r in 0..6 {
        scalars[1 + r] = ch.perm_challenges[r];
    }
    scalars[7] = ch.perm_additive;
    let scalars_dev = upload(context, &scalars);

    // const_challenge: alpha-power bank, index k = alpha^k. The v2 compiler does
    // NOT emit a `ConstChallenge` (or `ArgChallenge`) operand LANE — the alpha
    // power is the IMPLICIT column ordinal the kernel computes while walking
    // operands (compiler_v2/challenges.rs + macros.rs: "challenges are
    // column-indexed banks, not operand lanes"). So size the bank by the maximum
    // implicit ordinal the KERNEL will read, mirroring `gkr_fwd_interp_v2.cu`:
    //   - GateOutputFold (.cu:454): reads const_challenge[t] for t in 1..n_operands
    //     → candidate index = n_operands - 1.
    //   - VectorizedLookup / VectorLookupGate (.cu:542): reads
    //     const_challenge[col_k] for the k-th column GROUP → candidate index =
    //     n_groups - 1, where groups are decoded exactly as the kernel walks the
    //     operand region (read the term_count operand VALUE, then skip 1 constant
    //     lane + 2*term_count lanes per group).
    // Also extended below to cover any decoder fill alpha-power index
    // (generic_width-1) used by a DecoderMappedE4 gather.
    let mut max_cc_idx: u32 = 0;
    let mut has_cc = false;
    // Decode the base-field scalar VALUE of a term_count operand lane, mirroring
    // the kernel's `bf::into_canonical_u32(tc.base_coefficient_from_flat_idx(0))`
    // (interp_v2::ext_to_usize). The compiler always emits a constant scalar here
    // (`Special{ONE/ZERO}` or `Ldc{Const}`); anything else is not a valid
    // term_count lane, so fall back to 0 (it cannot extend the group count).
    let term_count_value = |op: &Operand| -> usize {
        match op {
            Operand::Ldc {
                sub: LdcSub::Special,
                idx,
            } => match *idx {
                gkr_eval_isa::isa_v2::SPECIAL_ONE => 1,
                _ => 0, // SPECIAL_ZERO / SPECIAL_NEG_ONE: not a positive count.
            },
            Operand::Ldc {
                sub: LdcSub::Const,
                idx,
            } => cf2.program.consts.get(*idx as usize).copied().unwrap_or(0) as usize,
            _ => 0,
        }
    };
    for ins in &cf2.program.instrs {
        if let Header::Macro { routine, n_operands } = ins.header {
            if routine == RoutineId::GateOutputFold as u8 {
                // Reads const_challenge[1 ..= n_operands-1].
                if n_operands >= 2 {
                    has_cc = true;
                    max_cc_idx = max_cc_idx.max(n_operands as u32 - 1);
                }
            } else if routine == RoutineId::VectorizedLookup as u8
                || routine == RoutineId::VectorLookupGate as u8
            {
                // Count column groups by walking the operand region exactly as the
                // kernel does; the (n_groups-1)-th group reads const_challenge.
                let ops = &ins.operands;
                let mut pos = 0usize;
                let mut n_groups: u32 = 0;
                while pos < ops.len() {
                    let term_count = term_count_value(&ops[pos]);
                    // term_count lane + constant_k lane + 2*term_count (coeff,col).
                    pos += 2 + 2 * term_count;
                    n_groups += 1;
                }
                if n_groups >= 2 {
                    has_cc = true;
                    max_cc_idx = max_cc_idx.max(n_groups - 1);
                }
            }
        }
    }
    // Decoder fill reads const_challenge[generic_width-1] (interp_v2 / the .cu),
    // so the bank must extend to that index when a decoder gather is present.
    let decoder_present = cf2
        .gathers
        .iter()
        .any(|g| g.kind == IndirectKind::DecoderMappedE4);
    if decoder_present && fixture.compiled_circuit.tables_ids_in_generic_lookups {
        let width = fixture.compiled_circuit.generic_lookup_tables_width as u32;
        if width > 0 {
            max_cc_idx = max_cc_idx.max(width - 1);
            has_cc = true;
        }
    }
    let cc_len = if has_cc { max_cc_idx as usize + 1 } else { 1 };
    let mut const_challenge = vec![E4::ZERO; cc_len];
    // [k] = alpha^k iteratively; [0] = ONE (alpha^0). alpha = lookup_alpha.
    let alpha = ch.alpha;
    let mut acc = E4::ONE;
    const_challenge[0] = acc;
    for slot in const_challenge.iter_mut().skip(1) {
        acc.mul_assign(&alpha);
        *slot = acc;
    }
    let cc_dev = upload(context, &const_challenge);

    // ----- Gather descriptor binding (desc_* arrays). Mirror cache_relation.rs /
    // lookup_helpers.cuh: bind each gather to the SAME production buffers the flat
    // cache launchers read. The forward compiler leaves the descriptor slot/len/
    // decoder fields None, so the SOURCE identity comes from gather_addrs[d] (the
    // cached GKRAddress) resolved through this layer's CacheKind. -----
    let stage1 = fixture_stage1(fixture);
    let cache_kind_by_addr: BTreeMap<GKRAddress, CacheKind> = cg_layer
        .caches
        .iter()
        .map(|c| (c.out.1, c.kind.clone()))
        .collect();
    let (setup_ptr, setup_len) = fixture.setup_table();
    let generic_lookup_base = setup_ptr; // VectorizedLookupSetup cache out == generic_lookup
    let decoder_pred_addr = fixture.decoder_predicate_address();
    let decoder_fill_alpha = if fixture.compiled_circuit.tables_ids_in_generic_lookups {
        fixture
            .compiled_circuit
            .generic_lookup_tables_width
            .saturating_sub(1) as u32
    } else {
        0
    };
    // Decoder fill = `alpha^(width-1) · table_id`; production gates `table_id` on
    // `tables_ids_in_generic_lookups && width > 0` (setup/mod.rs:253
    // `decoder_table_id_value`). When the circuit does NOT carry table ids in its
    // generic lookups (add_sub), `table_id == 0`, so the fill is ZERO — a disabled
    // (padding) decoder row contributes 0, not `alpha^k · Decoder`. Binding
    // `Decoder` unconditionally made the fill non-zero and broke the padding row.
    let decoder_table_id = if fixture.compiled_circuit.tables_ids_in_generic_lookups
        && fixture.compiled_circuit.generic_lookup_tables_width > 0
    {
        TableType::Decoder as u32
    } else {
        0
    };

    let n_descs = cf2.gathers.len();
    let mut desc_kind = vec![0u8; n_descs];
    let mut desc_n = vec![0u64; n_descs];
    let mut desc_mapping = vec![0u64; n_descs];
    let mut desc_n_len = vec![0u32; n_descs];
    let mut desc_mask = vec![0u64; n_descs];
    let mut desc_fill_alpha = vec![0u32; n_descs];
    let mut desc_table_id = vec![0u32; n_descs];
    let mut gather_bf_bufs: Vec<DeviceAllocation<BF>> = Vec::new();
    let mut inits_td_bufs: Vec<DeviceAllocation<E4>> = Vec::new();
    let mut unbound_gathers: Vec<String> = Vec::new();

    for (d, g) in cf2.gathers.iter().enumerate() {
        desc_kind[d] = gather_kind_u8(g.kind);
        // The value field (e4 vs bf) is derived from the kind on the device
        // (`desc_e4` in the .cu), so there is no per-desc field bitset — a
        // >32-gather circuit (bigint 139, blake2 381) would overflow a u32 one.
        // Default: no mapping / no length guard / no mask.
        desc_n_len[d] = 0xFFFF_FFFF;

        match g.kind {
            IndirectKind::RowIndexedSetupE4 => {
                // VectorizedLookupSetup reads setup COLUMN c row-indexed (NO
                // mapping). The generic_lookup table is column-major and
                // `generic_lookup_tables_width`-wide (8 for these circuits), so the
                // bare base is only column 0 — distinct setup descs (`Cached{c}`)
                // must read distinct columns. Production materializes column c
                // verbatim (row-indexed, zero-padded beyond the valid length) into
                // the resident `Cached{c}`, so that resident column IS this
                // gather's value table. Binding the bare base gave every setup
                // desc column 0, so the slot-6 grand-product Products read
                // colN*colN instead of colN*colM and mismatched production.
                if let Some(addr) = cf2.gather_addrs[d] {
                    if let Some(p) = resolve_addr(layer, &fixture.storage, addr) {
                        desc_n[d] = p as u64;
                    }
                }
                // No length guard: the resident `Cached{c}` IS production's
                // materialized setup column, already zero-padded by the cache
                // kernel with the SAME `gid < ln_len ? ln[gid] : 0` formula the
                // forward uses — so reading it row-indexed for all gid matches
                // production at every row (verified: guarding with the generic
                // length wrongly zeroed real last-row values).
                desc_n_len[d] = 0xFFFF_FFFF;
                if desc_n[d] == 0 {
                    unbound_gathers.push(format!(
                        "desc {d} RowIndexedSetupE4: no resident setup column for addr {:?}",
                        cf2.gather_addrs[d]
                    ));
                }
            }
            IndirectKind::MappedGenericE4 => {
                // VectorizedLookup plain: n[mapping[gid]] over generic_lookup.
                desc_n[d] = generic_lookup_base as u64;
                desc_mapping[d] = mapping_for_generic(cf2, stage1, d, &cache_kind_by_addr);
                if desc_mapping[d] == 0 {
                    unbound_gathers.push(format!(
                        "desc {d} MappedGenericE4: no generic mapping for addr {:?}",
                        cf2.gather_addrs[d]
                    ));
                }
            }
            IndirectKind::DecoderMappedE4 => {
                // VectorizedLookup decoder: n[mapping[gid]] + predicate mask + fill.
                desc_n[d] = generic_lookup_base as u64;
                desc_mapping[d] = stage1
                    .lookup_mappings
                    .decoder_mapping()
                    .map(|m| m.as_ptr() as u64)
                    .unwrap_or(0);
                if let Some(addr) = decoder_pred_addr {
                    // Bind the decoder predicate via the base-layer storage column
                    // (mirrors production cache_relation.rs:396
                    // `storage.get_base_layer(addr)`), NOT `resolve_addr`: the
                    // latter consults the per-layer `addr_resolve` map FIRST, which
                    // can return a different (replayed/aliased) column for this
                    // `BaseLayerMemory(machine_state.execute)` address and diverge
                    // at the padding row (the add_sub last-row mismatch). The
                    // predicate is base-field, so `storage_column` resolves it
                    // through `try_get_base_poly`, the same map `get_base_layer`
                    // reads.
                    if let Some((_e4, p)) = fixture.storage_column(addr) {
                        desc_mask[d] = p as u64;
                    }
                }
                desc_fill_alpha[d] = decoder_fill_alpha;
                desc_table_id[d] = decoder_table_id;
                if desc_mapping[d] == 0 || desc_mask[d] == 0 {
                    unbound_gathers.push(format!(
                        "desc {d} DecoderMappedE4: mapping={:#x} mask={:#x} (addr {:?})",
                        desc_mapping[d], desc_mask[d], cf2.gather_addrs[d]
                    ));
                }
            }
            IndirectKind::MappedVirtualBf => {
                // SingleColumnLookup: virtual_setup[mapping[gid]] (base field). The
                // value table is the materialized virtual-setup column; the mapping
                // is the range-check (width 16) or timestamp mapping.
                let (n_ptr, map_ptr) =
                    bind_mapped_virtual(context, cf2, stage1, d, &cache_kind_by_addr, t);
                if let Some(buf) = n_ptr {
                    desc_n[d] = buf.as_ptr() as u64;
                    gather_bf_bufs.push(buf);
                }
                desc_mapping[d] = map_ptr;
                if desc_n[d] == 0 || desc_mapping[d] == 0 {
                    unbound_gathers.push(format!(
                        "desc {d} MappedVirtualBf: n={:#x} mapping={:#x} (addr {:?})",
                        desc_n[d], desc_mapping[d], cf2.gather_addrs[d]
                    ));
                }
            }
            IndirectKind::InitsTeardownsHighAddr => {
                // id-20 launcher-deferred scalar `top_bits[set_idx] << shift`. The
                // value is a prover-runtime memory-argument constant the fixture
                // does NOT expose, so it cannot be bound here. Stage a 1-element
                // zero buffer (kernel reads row 0) and LOG the gap — the test must
                // skip / report any layer that emits this rather than mis-bind.
                let buf = upload(context, &[E4::ZERO]);
                desc_n[d] = buf.as_ptr() as u64;
                inits_td_bufs.push(buf);
                unbound_gathers.push(format!(
                    "desc {d} InitsTeardownsHighAddr set_idx={:?}: launcher-deferred \
                     top_bits<<shift not resolvable from the fixture (staged 0)",
                    g.inits_td_set_idx
                ));
            }
        }
    }

    // Upload the desc_* arrays.
    let desc_kind_dev = upload(context, &desc_kind);
    let desc_n_dev = upload(context, &desc_n);
    let desc_mapping_dev = upload(context, &desc_mapping);
    let desc_n_len_dev = upload(context, &desc_n_len);
    let desc_mask_dev = upload(context, &desc_mask);
    let desc_fill_alpha_dev = upload(context, &desc_fill_alpha);
    let desc_table_id_dev = upload(context, &desc_table_id);

    // ----- Program lanes + the matrix/output pointer tables. -----
    let lanes = gkr_eval_isa::isa_v2::encode::encode2(&cf2.program);
    let lanes_dev = upload(context, &lanes);
    let col_base_dev = upload(context, &col_base);
    let columns_dev = upload(context, &columns_host);
    let out_base_dev = upload(context, &out_base);
    let out_cols_dev = upload(context, &out_cols_host);
    let mut err_dev = upload(context, &[0u32]);

    context.get_exec_stream().synchronize().unwrap();

    let desc = InterpDesc2 {
        program_ldg: lanes_dev.as_ptr(),
        program_lanes: lanes.len() as u32,
        n_instr: cf2.program.instrs.len() as u32,
        columns: columns_dev.as_ptr() as *const *const u8,
        col_base: col_base_dev.as_ptr(),
        slot_is_e4,
        n_matrix_slots: n_slots as u32,
        consts: consts_dev.as_ptr(),
        const_challenge: cc_dev.as_ptr(),
        n_const_challenge: const_challenge.len() as u32,
        arg_challenge: ptr::null(),
        n_arg_challenge: 0,
        challenge_scalars: scalars_dev.as_ptr(),
        n_descs: n_descs as u32,
        desc_kind: if n_descs == 0 {
            ptr::null()
        } else {
            desc_kind_dev.as_ptr()
        },
        desc_n: if n_descs == 0 {
            ptr::null()
        } else {
            desc_n_dev.as_ptr() as *const *const u8
        },
        desc_mapping: if n_descs == 0 {
            ptr::null()
        } else {
            desc_mapping_dev.as_ptr() as *const *const u32
        },
        desc_n_len: if n_descs == 0 {
            ptr::null()
        } else {
            desc_n_len_dev.as_ptr()
        },
        desc_mask: if n_descs == 0 {
            ptr::null()
        } else {
            desc_mask_dev.as_ptr() as *const *const BF
        },
        desc_fill_alpha: if n_descs == 0 {
            ptr::null()
        } else {
            desc_fill_alpha_dev.as_ptr()
        },
        desc_table_id: if n_descs == 0 {
            ptr::null()
        } else {
            desc_table_id_dev.as_ptr()
        },
        out_columns: out_cols_dev.as_ptr() as *const *mut u8,
        out_base: out_base_dev.as_ptr(),
        out_is_e4,
        budget_cells: cf2.program.n_slot_cells as u32,
        count: t as u32,
        error_flag: err_dev.as_mut_ptr(),
    };

    InterpDesc2Setup {
        desc,
        out_columns,
        n_matrix_slots: n_slots,
        n_lanes: lanes.len(),
        unbound_gathers,
        _lanes_dev: lanes_dev,
        _consts_dev: consts_dev,
        _cc_dev: cc_dev,
        _scalars_dev: scalars_dev,
        _col_base_dev: col_base_dev,
        _columns_dev: columns_dev,
        _out_base_dev: out_base_dev,
        _out_cols_dev: out_cols_dev,
        _virtual_src: virtual_src,
        _gather_bf_bufs: gather_bf_bufs,
        _inits_td_bufs: inits_td_bufs,
        _desc_kind_dev: desc_kind_dev,
        _desc_n_dev: desc_n_dev,
        _desc_mapping_dev: desc_mapping_dev,
        _desc_n_len_dev: desc_n_len_dev,
        _desc_mask_dev: desc_mask_dev,
        _desc_fill_alpha_dev: desc_fill_alpha_dev,
        _desc_table_id_dev: desc_table_id_dev,
        _err_dev: err_dev,
    }
}

#[cfg(not(no_cuda))]
impl InterpDesc2Setup {
    /// The 1-element error-flag device buffer the kernel atomicOr's its
    /// `INTERP2_ERR_*` bits into. The parity test reads it back to assert a clean
    /// (0) launch.
    pub(super) fn err_dev(&self) -> &DeviceSlice<u32> {
        &self._err_dev[0..1]
    }
}

/// Map an `IndirectKind` to the device `GK_*` u8 (mirrors the `.cu` constants).
fn gather_kind_u8(kind: IndirectKind) -> u8 {
    match kind {
        IndirectKind::MappedVirtualBf => 0,
        IndirectKind::MappedGenericE4 => 1,
        IndirectKind::DecoderMappedE4 => 2,
        IndirectKind::RowIndexedSetupE4 => 3,
        IndirectKind::InitsTeardownsHighAddr => 4,
    }
}

/// Resolve the generic-mapping device pointer for a plain `MappedGenericE4`
/// gather: the cache's `lookup_set_index` selects the per-set generic mapping
/// (`stage1.lookup_mappings.generic_mapping(set_idx)`), exactly as
/// `cache_relation.rs` binds the flat VectorizedLookup. Returns 0 if the
/// gather's addr does not resolve to a same-layer VectorizedLookup cache.
#[cfg(not(no_cuda))]
fn mapping_for_generic(
    cf2: &CompiledForward2,
    stage1: &GpuGKRStage1Output,
    d: usize,
    cache_kind_by_addr: &BTreeMap<GKRAddress, CacheKind>,
) -> u64 {
    let Some(addr) = cf2.gather_addrs[d] else {
        return 0;
    };
    match cache_kind_by_addr.get(&addr) {
        Some(CacheKind::VectorizedLookup {
            lookup_set_index, ..
        }) => stage1
            .lookup_mappings
            .generic_mapping(*lookup_set_index)
            .as_ptr() as u64,
        _ => 0,
    }
}

/// Bind a `MappedVirtualBf` gather (SingleColumnLookup cache): the value table is
/// the materialized virtual-setup column (RangeCheck16Bits for width 16, else
/// RangeCheckTimestamp) and the mapping is the range-check / timestamp mapping
/// for the cache's `lookup_set_index` — mirrors `cache_relation.rs`'s
/// SingleColumnLookup arm. Returns `(Some(materialized n buffer), mapping ptr)`,
/// or `(None, 0)` if the gather addr is not a same-layer SingleColumnLookup.
#[cfg(not(no_cuda))]
fn bind_mapped_virtual(
    context: &ProverContext,
    cf2: &CompiledForward2,
    stage1: &GpuGKRStage1Output,
    d: usize,
    cache_kind_by_addr: &BTreeMap<GKRAddress, CacheKind>,
    t: usize,
) -> (Option<DeviceAllocation<BF>>, u64) {
    let Some(addr) = cf2.gather_addrs[d] else {
        return (None, 0);
    };
    match cache_kind_by_addr.get(&addr) {
        Some(CacheKind::SingleColumnLookup {
            lookup_set_index,
            range_check_width,
            ..
        }) => {
            let (poly, mapping): (VirtualSetupPoly, &DeviceSlice<u32>) = if *range_check_width == 16
            {
                (
                    VirtualSetupPoly::RangeCheck16Bits,
                    stage1.lookup_mappings.range_check_mapping(*lookup_set_index),
                )
            } else {
                (
                    VirtualSetupPoly::RangeCheckTimestamp,
                    stage1.lookup_mappings.timestamp_mapping(*lookup_set_index),
                )
            };
            let host_col = materialize_virtual_setup_column(poly, t);
            let n_buf = upload(context, &host_col);
            let map_ptr = mapping.as_ptr() as u64;
            (Some(n_buf), map_ptr)
        }
        _ => (None, 0),
    }
}

/// Read back a materialized output column as e4 host values (the column buffer is
/// E4-backed; for a bf column only the low limb is meaningful).
#[cfg(not(no_cuda))]
pub(super) fn readback_out_e4(buf: &DeviceAllocation<E4>, t: usize, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; t];
    memory_copy_async(&mut host[..], &buf[0..t], context.get_exec_stream()).unwrap();
    host
}

/// Read back a materialized BF output column with the matching element stride.
///
/// The kernel writes a bf-slot materialize output as a CONTIGUOUS bf column
/// (`gkr_fwd_interp_v2.cu:626` `store<bf>(reinterpret_cast<bf*>(ptr), ..., gid)`,
/// element-sized 4-byte stride), so row `gid` lands at byte `gid*4` in the buffer
/// — NOT at the 16-byte E4 stride `readback_out_e4` would assume. Reinterpret the
/// buffer's first `t*4` bytes as the bf column the kernel actually wrote (same
/// reinterpret `read_golden_bf` already uses for the production golden).
#[cfg(not(no_cuda))]
pub(super) fn readback_out_bf(buf: &DeviceAllocation<E4>, t: usize, context: &ProverContext) -> Vec<BF> {
    // SAFETY: the kernel stored `t` contiguous bf elements into this buffer (a
    // bf materialize output). The buffer was allocated for `t` E4 elements
    // (t*16 bytes >= t*4 bytes), so the first `t` BF elements are in-bounds.
    let slice = unsafe { DeviceSlice::from_raw_parts(buf.as_ptr() as *const BF, t) };
    let mut host = vec![BF::ZERO; t];
    memory_copy_async(&mut host[..], slice, context.get_exec_stream()).unwrap();
    host
}

/// Read the production FLAT golden for an output address as e4 host values.
#[cfg(not(no_cuda))]
pub(super) fn read_golden_e4(ptr: *const u8, t: usize, context: &ProverContext) -> Vec<E4> {
    // SAFETY: `ptr` is a resident e4 column base of >= t elements (storage_column
    // returned is_e4 == true). Reinterpret as a device slice for the readback.
    let slice = unsafe { DeviceSlice::from_raw_parts(ptr as *const E4, t) };
    let mut host = vec![E4::ZERO; t];
    memory_copy_async(&mut host[..], slice, context.get_exec_stream()).unwrap();
    host
}

/// Read the production FLAT golden for a bf output address as bf host values.
#[cfg(not(no_cuda))]
pub(super) fn read_golden_bf(ptr: *const u8, t: usize, context: &ProverContext) -> Vec<BF> {
    // SAFETY: `ptr` is a resident bf column base of >= t elements.
    let slice = unsafe { DeviceSlice::from_raw_parts(ptr as *const BF, t) };
    let mut host = vec![BF::ZERO; t];
    memory_copy_async(&mut host[..], slice, context.get_exec_stream()).unwrap();
    host
}

/// The base-field (low-limb) view of a materialized e4 output cell — the kernel
/// stores a bf result via `write_cell(..., is_e4=false, ...)`, writing only limb
/// 0, so a bf output compare reads limb 0 of the e4-backed buffer.
#[cfg(not(no_cuda))]
pub(super) fn e4_low_limb(v: E4) -> BF {
    <E4 as FieldExtension<BF>>::into_coeffs(v)[0]
}
