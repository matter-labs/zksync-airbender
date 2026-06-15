//! Phase-3 Task 3.2: the GATHER INDEX-PATH ORACLE (spec R10).
//!
//! Proves the v2 interpreter resolves each gather descriptor THROUGH its index
//! arithmetic per row. The tables are ROW-VARYING and the mappings are
//! NON-TRIVIAL (non-identity permutations), so a constant fill cannot hide a
//! stride / off-by-one / mapping bug — `resolve_gather` must read the value
//! table via `mapping[gid]` (mapped variants) or `gid` (row-indexed) for the
//! per-row expectation to hold.
//!
//! Decoder reference (CUDA `lookup_helpers.cuh:58-69`, Rust
//! `cache_relation.rs:382-419`): a decoder-mapped gather reads `n[mapping[gid]]`,
//! then applies a per-row base-field PREDICATE mask `decoder_mask[gid]`; on the
//! masked-out branch (`mask.limb == 0`) it substitutes the FILL scalar
//! `α^fill_alpha_power · table_id` (`gkr_forward_setup_generic_lookup:409-413`).
//! The interpreter computes that fill itself from `DecoderSpec` + the α-power
//! bank — it is not handed a pre-resolved value (spec finding 1).

use field::{Field, PrimeField};
use gkr_eval_isa::compiler_v2::gather::{DecoderSpec, GatherDescriptor};
use gkr_eval_isa::eval_ref::{Bf, Ext, lift};
use gkr_eval_isa::interp_v2::*;
use gkr_eval_isa::isa_v2::*;

fn bf(v: u32) -> Bf {
    Bf::from_u32_with_reduction(v)
}

/// Build a descriptor of the given kind. `decoder` is attached only for the
/// decoder variant; the slot/len fields are not read by `resolve_gather`.
fn descriptor(
    kind: IndirectKind,
    field_ext: bool,
    decoder: Option<DecoderSpec>,
) -> GatherDescriptor {
    GatherDescriptor {
        kind,
        field_ext,
        n_slot: None,
        mapping_slot: None,
        n_len: None,
        decoder,
    }
}

#[test]
fn gather_tracks_table_mapping_per_row() {
    // ----------------------------------------------------------------------
    // Descriptor 0: MappedVirtualBf (SingleColumnLookup, base).
    // Descriptor 1: MappedGenericE4 (VectorizedLookup plain, ext).
    //   Both read n[mapping[gid]] through a per-row mapping. Use a value table
    //   whose entries differ from their indices (row-varying), and a mapping
    //   that is a NON-IDENTITY permutation so any stride/off-by-one bug in the
    //   index path surfaces.
    //
    //   value table n      = [100, 101, 102, 103, 104]   (n[i] = 100 + i)
    //   mapping            = [4, 2, 0, 3, 1]              (reversed-ish perm)
    //   so resolve(gid) == n[mapping[gid]] == 100 + mapping[gid]:
    //     gid 0 -> n[4] = 104,  gid 1 -> n[2] = 102,  gid 2 -> n[0] = 100,
    //     gid 3 -> n[3] = 103,  gid 4 -> n[1] = 101.
    // ----------------------------------------------------------------------
    let value_table: Vec<Ext> = (0..5).map(|i| lift(bf(100 + i))).collect();
    let mapping: Vec<u32> = vec![4, 2, 0, 3, 1];
    let expected_mapped: Vec<Ext> = mapping.iter().map(|&m| lift(bf(100 + m))).collect();

    // ----------------------------------------------------------------------
    // Descriptor 2: DecoderMappedE4 (VectorizedLookup w/ decoder, ext).
    //   Same mapped read, plus a per-row predicate. decoder_mask[gid] is a
    //   base-field flag: mask != 0 => use n[mapping[gid]]; mask == 0 => fill.
    //   The fill scalar is computed by the interpreter as
    //     α^fill_alpha_power · table_id
    //   from the α-power bank + DecoderSpec (NOT handed in pre-resolved).
    //
    //   mask = [1, 0, 1, 0, 1]: rows 1 and 3 are masked out (use fill).
    //   fill_alpha_power = 3, table_id = 7, α = 2 (lifted):
    //     α^3 = 8, fill = 8 * 7 = 56.
    // ----------------------------------------------------------------------
    let alpha = lift(bf(2));
    // α-power bank: alpha_powers[k] = α^k.
    let mut alpha_powers = vec![Ext::ONE];
    for _ in 1..6 {
        let mut next = *alpha_powers.last().unwrap();
        next.mul_assign(&alpha);
        alpha_powers.push(next);
    }
    let fill_alpha_power: u16 = 3;
    let table_id: u32 = 7;
    // fill = α^3 * table_id = 8 * 7 = 56.
    let mut fill = alpha_powers[fill_alpha_power as usize];
    fill.mul_assign(&lift(bf(table_id)));
    let decoder_mask: Vec<Bf> = vec![bf(1), bf(0), bf(1), bf(0), bf(1)];

    // ----------------------------------------------------------------------
    // Descriptor 3: RowIndexedSetupE4 (VectorizedLookupSetup, ext).
    //   No mapping: read n[gid], zero-padded beyond n_len. Use a DISTINCT
    //   row-varying value table so a wrong-descriptor index would be caught.
    //   n_setup = [200, 201, 202], n_len = 3: gids 0..2 read the table,
    //   gid 3 (out of range) must return Ext::ZERO (length guard).
    // ----------------------------------------------------------------------
    let setup_table: Vec<Ext> = (0..3).map(|i| lift(bf(200 + i))).collect();
    let setup_len = setup_table.len();

    // Assemble the per-descriptor tables. Index by descriptor index.
    let tables = GatherTables {
        n: vec![
            value_table.clone(),
            value_table.clone(),
            value_table.clone(),
            setup_table.clone(),
        ],
        mapping: vec![
            mapping.clone(),
            mapping.clone(),
            mapping.clone(),
            Vec::new(),
        ],
        n_len: vec![None, None, None, Some(setup_len)],
        decoder_mask: vec![None, None, Some(decoder_mask.clone()), None],
        alpha_powers: alpha_powers.clone(),
    };

    let d_mapped_bf = descriptor(IndirectKind::MappedVirtualBf, false, None);
    let d_mapped_e4 = descriptor(IndirectKind::MappedGenericE4, true, None);
    let d_decoder = descriptor(
        IndirectKind::DecoderMappedE4,
        true,
        Some(DecoderSpec {
            fill_alpha_power,
            table_id,
        }),
    );
    let d_setup = descriptor(IndirectKind::RowIndexedSetupE4, true, None);

    // --- MappedVirtualBf (desc 0) and MappedGenericE4 (desc 1): per row ---
    for gid in 0..mapping.len() {
        assert_eq!(
            resolve_gather(&d_mapped_bf, gid, &tables, 0),
            expected_mapped[gid],
            "MappedVirtualBf gid {gid}: expected n[mapping[{gid}]] = n[{}]",
            mapping[gid]
        );
        assert_eq!(
            resolve_gather(&d_mapped_e4, gid, &tables, 1),
            expected_mapped[gid],
            "MappedGenericE4 gid {gid}: expected n[mapping[{gid}]] = n[{}]",
            mapping[gid]
        );
    }
    // Caught-bug witness: a non-identity mapping means resolve(gid) != n[gid]
    // for the permuted rows. gid 0 maps to row 4, so it must NOT equal n[0].
    assert_ne!(
        resolve_gather(&d_mapped_e4, 0, &tables, 1),
        value_table[0],
        "non-identity mapping: resolve(0) must be n[mapping[0]]=n[4], not n[0]"
    );

    // --- DecoderMappedE4 (desc 2): in-range branch AND masked-out branch ---
    for gid in 0..mapping.len() {
        let got = resolve_gather(&d_decoder, gid, &tables, 2);
        if decoder_mask[gid].is_zero() {
            // masked out -> fill scalar α^fill_alpha_power * table_id.
            assert_eq!(
                got, fill,
                "DecoderMappedE4 gid {gid}: masked out, expected fill"
            );
        } else {
            // enabled -> mapped value n[mapping[gid]].
            assert_eq!(
                got, expected_mapped[gid],
                "DecoderMappedE4 gid {gid}: enabled, expected mapped n[{}]",
                mapping[gid]
            );
        }
    }
    // Explicit branch witnesses: gid 0 enabled (mapped), gid 1 masked (fill).
    assert_eq!(
        resolve_gather(&d_decoder, 0, &tables, 2),
        expected_mapped[0]
    );
    assert_eq!(resolve_gather(&d_decoder, 1, &tables, 2), fill);

    // --- RowIndexedSetupE4 (desc 3): n[gid] in range, ZERO out of range ---
    for gid in 0..setup_len {
        assert_eq!(
            resolve_gather(&d_setup, gid, &tables, 3),
            setup_table[gid],
            "RowIndexedSetupE4 gid {gid}: expected n[{gid}] = {}",
            200 + gid
        );
    }
    // Out-of-range row exercises the LOOKUP_SETUP length guard -> Ext::ZERO.
    assert_eq!(
        resolve_gather(&d_setup, setup_len, &tables, 3),
        Ext::ZERO,
        "RowIndexedSetupE4 gid {setup_len} >= n_len {setup_len}: expected ZERO"
    );
}
