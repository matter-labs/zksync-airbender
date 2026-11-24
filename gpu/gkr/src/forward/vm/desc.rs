//! Rust half of the forward VM descriptor ABI.
// --- caps (mirror the FWD_VM_* constexprs in fwd_vm.cuh) ---------------------
pub(crate) const PROGRAM_CAP: usize = 12288;
pub(crate) const CONST_CAP: usize = 64;
pub(crate) const ARG_DERIVED_E4_CAP: usize = 12;
pub(crate) const DESC_CAP: usize = 370;
pub(crate) const CONST_DERIVED_E4_CAP: usize = 8;
pub(crate) const SOURCE_WINDOW_COUNT: usize = 16;
pub(crate) const LAYER_CAP: usize = 8;
pub(crate) const DST_SLOT_COUNT: usize = 16;
pub(crate) const MAPPING_ARENA_COUNT: usize = 3;
pub(crate) const FUSED_REDUCTION_ROUNDS: usize = 7;
pub(crate) const REDUCTION_PAIR_CAP: usize = 5;
pub(crate) const REDUCTION_PAIR_PAIRWISE2: u32 = 0;
pub(crate) const REDUCTION_PAIR_LOOKUP: u32 = 1;

// --- special-descriptor strategy kinds (packed-desc `kind` field) ------------
pub(crate) const SD_SINGLE_COLUMN: u32 = 0;
pub(crate) const SD_AGGREGATE: u32 = 1;
pub(crate) const SD_SETUP: u32 = 2;
pub(crate) const SD_DECODER: u32 = 3;
pub(crate) const SD_VIRTUAL: u32 = 4;
pub(crate) const SD_INITS_TOP_BITS: u32 = 5;

// --- mapping-arena selectors (packed-desc `arena` field) ---------------------
pub(crate) const ARENA_GENERIC_FAMILY: u32 = 0;
pub(crate) const ARENA_RANGE_CHECK_16: u32 = 1;
pub(crate) const ARENA_TIMESTAMP: u32 = 2;

// --- SD_VIRTUAL `vkind` codes -------------------------------------------------
pub(crate) const GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS: u32 = 2;
pub(crate) const GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP: u32 = 3;
pub(crate) const GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW: u32 = 4;
pub(crate) const GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH: u32 = 5;
pub(crate) const VKIND_RANGE_CHECK_16_BITS: u32 = GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS;
pub(crate) const VKIND_RANGE_CHECK_TIMESTAMP: u32 = GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP;
pub(crate) const VKIND_INITS_AND_TEARDOWNS_LOW: u32 =
    GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW;
pub(crate) const VKIND_INITS_AND_TEARDOWNS_HIGH: u32 =
    GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH;

const _: () = {
    use gpu_gkr_compiler::KIND_ORDER;

    use crate::upstream::VirtualSetupKind;
    assert!(KIND_ORDER.len() == 4);
    assert!(matches!(
        &KIND_ORDER[(VKIND_RANGE_CHECK_16_BITS - 2) as usize],
        VirtualSetupKind::RangeCheck16Bits
    ));
    assert!(matches!(
        &KIND_ORDER[(VKIND_RANGE_CHECK_TIMESTAMP - 2) as usize],
        VirtualSetupKind::RangeCheckTimestamp
    ));
    assert!(matches!(
        &KIND_ORDER[(VKIND_INITS_AND_TEARDOWNS_LOW - 2) as usize],
        VirtualSetupKind::InitsAndTeardownsLow
    ));
    assert!(matches!(
        &KIND_ORDER[(VKIND_INITS_AND_TEARDOWNS_HIGH - 2) as usize],
        VirtualSetupKind::InitsAndTeardownsHigh
    ));
};

// --- packed per-descriptor u32 -------------------------------------------------
// { kind:3 [0..3) | arena:2 [3..5) | set_index:16 [5..21) | vkind:3 [21..24) |
//   rsvd:8 [24..32) } — set_index needs 16 bits (blake2 L0 has 208 generic
// sets); vkind is the native `gkr_base_source_kind` value (2..=5) stored
// VERBATIM (../support/descriptors.cuh:12-18; pinned by the const asserts
// above), or the const-derived-E4 slot for SD_DECODER and SD_SETUP.
pub(crate) const DESC_KIND_SHIFT: u32 = 0;
#[cfg(test)]
pub(crate) const DESC_KIND_MASK: u32 = 0x7;
pub(crate) const DESC_ARENA_SHIFT: u32 = 3;
#[cfg(test)]
pub(crate) const DESC_ARENA_MASK: u32 = 0x3;
pub(crate) const DESC_SET_INDEX_SHIFT: u32 = 5;
#[cfg(test)]
pub(crate) const DESC_SET_INDEX_MASK: u32 = 0xffff;
pub(crate) const DESC_VKIND_SHIFT: u32 = 21;
#[cfg(test)]
pub(crate) const DESC_VKIND_MASK: u32 = 0x7;

/// Pack one special descriptor into its wire u32. Fields the kind does not use
/// must be passed as 0 (the encoder asserts range, not relevance).
pub(crate) fn pack_desc(kind: u32, arena: u32, set_index: u16, vkind: u32) -> u32 {
    assert!(kind <= SD_INITS_TOP_BITS, "desc kind {kind} out of range");
    assert!(arena <= ARENA_TIMESTAMP, "desc arena {arena} out of range");
    if kind == SD_DECODER || kind == SD_SETUP {
        assert!(
            vkind < CONST_DERIVED_E4_CAP as u32,
            "const-derived-E4 slot {vkind} out of range"
        );
    } else {
        assert!(
            vkind == 0 || (2..=5).contains(&vkind),
            "desc vkind {vkind} out of range"
        );
    }
    (kind << DESC_KIND_SHIFT)
        | (arena << DESC_ARENA_SHIFT)
        | ((set_index as u32) << DESC_SET_INDEX_SHIFT)
        | (vkind << DESC_VKIND_SHIFT)
}

/// Decode counterpart of [`pack_desc`] — `(kind, arena, set_index, vkind)`.
/// The kernel does the same shifts inline; this exists for tests/disassembly.
#[cfg(test)]
pub(crate) fn unpack_desc(desc: u32) -> (u32, u32, u16, u32) {
    (
        (desc >> DESC_KIND_SHIFT) & DESC_KIND_MASK,
        (desc >> DESC_ARENA_SHIFT) & DESC_ARENA_MASK,
        ((desc >> DESC_SET_INDEX_SHIFT) & DESC_SET_INDEX_MASK) as u16,
        (desc >> DESC_VKIND_SHIFT) & DESC_VKIND_MASK,
    )
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct FwdVmLayer {
    pub program_offset: u16,
    pub instruction_count: u16,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct FwdVmReductionPair<F> {
    pub input: [*const F; 2],
    pub round_outputs: [[*mut F; 2]; FUSED_REDUCTION_ROUNDS],
    pub kind: u32,
    pub reserved: u32,
}
