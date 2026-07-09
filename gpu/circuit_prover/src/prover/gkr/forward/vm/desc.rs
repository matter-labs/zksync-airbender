//! fwd-VM v2 descriptor ABI (Task 7): the Rust mirror of `fwd_vm_desc`
//! (`native/prover/gkr/forward/fwd_vm.cuh`) — ONE struct, passed by value as a
//! `__grid_constant__` kernel parameter (param-space limit 32,764 B).
//!
//! Keep field-for-field with the CUDA side. Field ORDER deviates from the
//! spec-§2 sketch on purpose: `e4`/`E4` is 16-aligned, so fields are grouped
//! by descending alignment (E4 -> pointers -> u32 -> u16) to make the layout
//! padding-free and the exact-size assert stable.
//!
//! Caps come from the corpus census (`gkr_eval_isa/tests/fwd_vm_desc_census.rs`,
//! maxima across all 11 committed with-caches fixtures: lanes 6574, consts 27,
//! arg challenges 7, const challenges 1, descs 296) + margin. Overflow policy:
//! program overflow falls back to `program_ldg`; every other cap is a hard
//! lowering error (no fallback).

use crate::primitives::field::{BF, E4};

// --- caps (mirror the FWD_VM_* constexprs in fwd_vm.cuh) ---------------------
pub(crate) const PROGRAM_CAP: usize = 12288; // u16 lanes, 24 KB inline
pub(crate) const CONST_CAP: usize = 40; // BF constants
pub(crate) const ARG_CHALLENGE_CAP: usize = 12; // schedule-time E4 challenges
pub(crate) const DESC_CAP: usize = 370; // packed special descriptors
pub(crate) const CONST_CHALLENGE_CAP: usize = 8; // Task-8 __constant__ E4 bank (not in this struct)
pub(crate) const SLOT_COUNT: usize = 16; // field-qualified column slots
pub(crate) const MAPPING_ARENA_COUNT: usize = 3; // generic_family / range_check_16 / timestamp

// --- special-descriptor strategy kinds (packed-desc `kind` field) ------------
pub(crate) const SD_SINGLE_COLUMN: u32 = 0; // PeekSingleColumn: lift(mapping[row])
pub(crate) const SD_AGGREGATE: u32 = 1; // PeekAggregate: table[mapping[row]]
pub(crate) const SD_SETUP: u32 = 2; // PeekSetup: row < table_len ? table[row] : 0
pub(crate) const SD_DECODER: u32 = 3; // PeekDecoder: mask[row] != 0 ? table[mapping[row]] : *fill
pub(crate) const SD_VIRTUAL: u32 = 4; // VirtualSetup: lift(n(vkind, gid)), no memory reads

// --- mapping-arena selectors (packed-desc `arena` field) ---------------------
pub(crate) const ARENA_GENERIC_FAMILY: u32 = 0;
pub(crate) const ARENA_RANGE_CHECK_16: u32 = 1;
pub(crate) const ARENA_TIMESTAMP: u32 = 2;

// --- SD_VIRTUAL `vkind` codes -------------------------------------------------
// vkind == `gkr_eval_isa::fwd::source::KIND_ORDER` index == native
// `gkr_base_source_kind` value - VKIND_NATIVE_BIAS
// (`native/prover/gkr/support/descriptors.cuh:12-18`: the four
// GKR_BASE_SOURCE_VIRTUAL_* variants are 2..=5, in KIND_ORDER order).
pub(crate) const VKIND_NATIVE_BIAS: u32 = 2;
pub(crate) const VKIND_RANGE_CHECK_16_BITS: u32 = 0;
pub(crate) const VKIND_RANGE_CHECK_TIMESTAMP: u32 = 1;
pub(crate) const VKIND_INITS_AND_TEARDOWNS_LOW: u32 = 2;
pub(crate) const VKIND_INITS_AND_TEARDOWNS_HIGH: u32 = 3;

/// Drift guard: the vkind codes above, biased by `VKIND_NATIVE_BIAS`, must
/// equal the native `gkr_base_source_kind` values (descriptors.cuh:12-18), and
/// the codes must stay in `KIND_ORDER` order (index == code) — `KIND_ORDER` is
/// the single upstream source of truth for the wire code.
const _: () = {
    use crate::upstream::VirtualSetupKind::*;
    use gkr_eval_isa::fwd::source::KIND_ORDER;
    // native gkr_base_source_kind values (descriptors.cuh:12-18)
    const GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS: u32 = 2;
    const GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP: u32 = 3;
    const GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW: u32 = 4;
    const GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH: u32 = 5;
    assert!(
        VKIND_RANGE_CHECK_16_BITS + VKIND_NATIVE_BIAS
            == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS
    );
    assert!(
        VKIND_RANGE_CHECK_TIMESTAMP + VKIND_NATIVE_BIAS
            == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP
    );
    assert!(
        VKIND_INITS_AND_TEARDOWNS_LOW + VKIND_NATIVE_BIAS
            == GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW
    );
    assert!(
        VKIND_INITS_AND_TEARDOWNS_HIGH + VKIND_NATIVE_BIAS
            == GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH
    );
    // KIND_ORDER index == vkind code (a 5th upstream kind fails here loudly:
    // it would also need a 3rd vkind bit and a new native enum value).
    assert!(KIND_ORDER.len() == 4);
    assert!(matches!(
        KIND_ORDER[VKIND_RANGE_CHECK_16_BITS as usize],
        RangeCheck16Bits
    ));
    assert!(matches!(
        KIND_ORDER[VKIND_RANGE_CHECK_TIMESTAMP as usize],
        RangeCheckTimestamp
    ));
    assert!(matches!(
        KIND_ORDER[VKIND_INITS_AND_TEARDOWNS_LOW as usize],
        InitsAndTeardownsLow
    ));
    assert!(matches!(
        KIND_ORDER[VKIND_INITS_AND_TEARDOWNS_HIGH as usize],
        InitsAndTeardownsHigh
    ));
};

// --- packed per-descriptor u32 -------------------------------------------------
// { kind:3 [0..3) | arena:2 [3..5) | set_index:16 [5..21) | vkind:2 [21..23) |
//   rsvd:9 [23..32) } — set_index needs 16 bits (blake2 L0 has 208 generic sets).
pub(crate) const DESC_KIND_SHIFT: u32 = 0;
pub(crate) const DESC_KIND_MASK: u32 = 0x7;
pub(crate) const DESC_ARENA_SHIFT: u32 = 3;
pub(crate) const DESC_ARENA_MASK: u32 = 0x3;
pub(crate) const DESC_SET_INDEX_SHIFT: u32 = 5;
pub(crate) const DESC_SET_INDEX_MASK: u32 = 0xffff;
pub(crate) const DESC_VKIND_SHIFT: u32 = 21;
pub(crate) const DESC_VKIND_MASK: u32 = 0x3;

/// Pack one special descriptor into its wire u32. Fields the kind does not use
/// must be passed as 0 (the encoder asserts range, not relevance).
pub(crate) fn pack_desc(kind: u32, arena: u32, set_index: u16, vkind: u32) -> u32 {
    assert!(kind <= SD_VIRTUAL, "desc kind {kind} out of range");
    assert!(arena <= ARENA_TIMESTAMP, "desc arena {arena} out of range");
    assert!(vkind <= DESC_VKIND_MASK, "desc vkind {vkind} out of range");
    (kind << DESC_KIND_SHIFT)
        | (arena << DESC_ARENA_SHIFT)
        | ((set_index as u32) << DESC_SET_INDEX_SHIFT)
        | (vkind << DESC_VKIND_SHIFT)
}

/// Decode counterpart of [`pack_desc`] — `(kind, arena, set_index, vkind)`.
/// The kernel does the same shifts inline; this exists for tests/disassembly.
pub(crate) fn unpack_desc(desc: u32) -> (u32, u32, u16, u32) {
    (
        (desc >> DESC_KIND_SHIFT) & DESC_KIND_MASK,
        (desc >> DESC_ARENA_SHIFT) & DESC_ARENA_MASK,
        ((desc >> DESC_SET_INDEX_SHIFT) & DESC_SET_INDEX_MASK) as u16,
        (desc >> DESC_VKIND_SHIFT) & DESC_VKIND_MASK,
    )
}

/// The fwd-VM v2 kernel parameter — mirror of CUDA `fwd_vm_desc`
/// (`native/prover/gkr/forward/fwd_vm.cuh`), field-for-field. Offsets in the
/// comments are byte offsets shared by both sides (zero internal padding).
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct FwdVmDesc {
    // schedule-time-known challenges, inline (16-aligned E4 first: zero padding)
    pub arg_challenge: [E4; ARG_CHALLENGE_CAP], // 0, 192 B
    // program oversize fallback; null when the program is inline (expected always)
    pub program_ldg: *const u16, // 192
    // column geometry: a slot IS one homogeneous matrix; ONE table serves both
    // reads and GlobalMaterialize writes: column c of slot s is
    // base[s] + c * stride_bytes[s] for load and store alike.
    pub base: [*mut u8; SLOT_COUNT], // 200
    // special-descriptor header (all schedule-time-known): 3 column-major u32
    // mapping arenas (column stride = `count`), the ONE shared generic-lookup
    // E4 table (contents runtime-filled), the per-circuit execute-predicate
    // mask column (or null), and the 1-element decoder-fill device slot —
    // runtime challenge-dependent, POINTER, never by value.
    pub mapping_arena: [*const u32; MAPPING_ARENA_COUNT], // 328
    pub table: *const E4,                                 // 352
    pub mask: *const BF,                                  // 360
    pub fill: *const E4,                                  // 368
    // program header
    pub n_instr: u32,       // 376
    pub program_lanes: u32, // 380
    // column geometry, continued
    pub stride_bytes: [u32; SLOT_COUNT], // 384
    // banks, inline (schedule-time known)
    pub n_consts: u32,           // 448
    pub consts: [BF; CONST_CAP], // 452, Montgomery
    pub n_arg_challenge: u32,    // 612
    // special descriptors
    pub n_descs: u32, // 616
    // used length of the Task-8 __constant__ bank; read only under VALIDATE
    pub n_const_challenge: u32, // 620
    pub table_len: u32,         // 624
    // per-desc packed u32 (bit split above)
    pub descs: [u32; DESC_CAP], // 628, 1,480 B
    // geometry
    pub count: u32, // 2108: rows (= trace_len = mapping-arena column stride)
    // program, inline 16-bit wire lanes (gkr_eval_isa::fwd::encode)
    pub program: [u16; PROGRAM_CAP], // 2112, 24,576 B
}

/// ABI size guards, paired with the CUDA `static_assert`s in `fwd_vm.cuh`.
const _: () = {
    assert!(
        core::mem::size_of::<FwdVmDesc>() == 26688,
        "fwd_vm_desc/FwdVmDesc ABI size drift"
    );
    assert!(
        core::mem::size_of::<FwdVmDesc>() <= 32764,
        "FwdVmDesc exceeds the __grid_constant__ param budget"
    );
    assert!(
        core::mem::align_of::<FwdVmDesc>() == 16,
        "FwdVmDesc alignment drift (E4 is 16-aligned)"
    );
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pack_desc_round_trips_the_bit_split() {
        // Every field at its corpus-realistic extreme plus the encodable max.
        let cases: &[(u32, u32, u16, u32)] = &[
            (SD_SINGLE_COLUMN, ARENA_RANGE_CHECK_16, 0, 0),
            (SD_SINGLE_COLUMN, ARENA_TIMESTAMP, 86, 0),
            (SD_AGGREGATE, ARENA_GENERIC_FAMILY, 207, 0),
            (SD_SETUP, 0, 0, 0),
            (SD_DECODER, ARENA_GENERIC_FAMILY, 208, 0),
            (SD_VIRTUAL, 0, 0, VKIND_RANGE_CHECK_16_BITS),
            (SD_VIRTUAL, 0, 0, VKIND_INITS_AND_TEARDOWNS_HIGH),
            (SD_VIRTUAL, ARENA_TIMESTAMP, u16::MAX, 3),
        ];
        for &(kind, arena, set_index, vkind) in cases {
            let packed = pack_desc(kind, arena, set_index, vkind);
            assert_eq!(
                unpack_desc(packed),
                (kind, arena, set_index, vkind),
                "round-trip failed for kind={kind} arena={arena} set_index={set_index} vkind={vkind}"
            );
        }
    }

    #[test]
    fn desc_bit_fields_do_not_overlap() {
        // Each field alone occupies its own bit span; reserved bits stay zero.
        // Raw shifts (not pack_desc): kind = DESC_KIND_MASK is deliberately
        // outside pack_desc's SD_* range check.
        let kind = DESC_KIND_MASK << DESC_KIND_SHIFT;
        let arena = DESC_ARENA_MASK << DESC_ARENA_SHIFT;
        let set_index = pack_desc(0, 0, u16::MAX, 0);
        let vkind = pack_desc(0, 0, 0, DESC_VKIND_MASK);
        assert_eq!(kind & arena, 0);
        assert_eq!((kind | arena) & set_index, 0);
        assert_eq!((kind | arena | set_index) & vkind, 0);
        assert_eq!(
            kind | arena | set_index | vkind,
            0x007f_ffff,
            "rsvd bits [23..32) must stay zero"
        );
    }

    #[test]
    #[should_panic(expected = "desc kind")]
    fn pack_desc_rejects_out_of_range_kind() {
        pack_desc(SD_VIRTUAL + 1, 0, 0, 0);
    }

    #[test]
    fn vkind_codes_match_gkr_eval_isa_wire_codes() {
        use cs::gkr_compiler::dag_ir::VirtualSetupKind::*;
        use gkr_eval_isa::fwd::source::virtual_setup_kind_code;
        assert_eq!(
            virtual_setup_kind_code(&RangeCheck16Bits),
            VKIND_RANGE_CHECK_16_BITS
        );
        assert_eq!(
            virtual_setup_kind_code(&RangeCheckTimestamp),
            VKIND_RANGE_CHECK_TIMESTAMP
        );
        assert_eq!(
            virtual_setup_kind_code(&InitsAndTeardownsLow),
            VKIND_INITS_AND_TEARDOWNS_LOW
        );
        assert_eq!(
            virtual_setup_kind_code(&InitsAndTeardownsHigh),
            VKIND_INITS_AND_TEARDOWNS_HIGH
        );
    }
}
