//! Rust half of the forward VM descriptor ABI.

use gpu_core::primitives::field::{BF, E4};

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
    use crate::upstream::VirtualSetupKind;
    use gpu_gkr_compiler::KIND_ORDER;
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
// above).
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
    if kind == SD_DECODER {
        assert!(
            vkind < CONST_DERIVED_E4_CAP as u32,
            "decoder const-derived-E4 slot {vkind} out of range"
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
fn unpack_desc(desc: u32) -> (u32, u32, u16, u32) {
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
pub(crate) struct FwdVmDesc {
    pub arg_derived_e4: [E4; ARG_DERIVED_E4_CAP],
    pub source_base: [*mut u8; SOURCE_WINDOW_COUNT],
    pub dst_base: [*mut u8; DST_SLOT_COUNT],
    pub mapping_arena: [*const u32; MAPPING_ARENA_COUNT],
    pub table: *const E4,
    pub mask: *const BF,
    pub source_stride_bytes: [u32; SOURCE_WINDOW_COUNT],
    pub dst_stride_bytes: [u32; DST_SLOT_COUNT],
    pub consts: [BF; CONST_CAP],
    pub table_len: u32,
    pub descs: [u32; DESC_CAP],
    pub count: u32,
    pub layer_count: u32,
    pub layers: [FwdVmLayer; LAYER_CAP],
    pub program: [u16; PROGRAM_CAP],
}

/// ABI size guards, paired with the CUDA `static_assert`s in `fwd_vm.cuh`.
const _: () = {
    assert!(core::mem::size_of::<FwdVmLayer>() == 4);
    assert!(core::mem::size_of::<FwdVmDesc>() == 26_976);
    assert!(core::mem::size_of::<FwdVmDesc>() <= 32_764);
    assert!(core::mem::align_of::<FwdVmDesc>() == 16);
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn desc_layout_matches_the_cuda_abi() {
        use core::mem::{align_of, offset_of, size_of};

        assert_eq!(size_of::<FwdVmLayer>(), 4);
        assert_eq!(align_of::<FwdVmLayer>(), 2);
        assert_eq!(offset_of!(FwdVmLayer, program_offset), 0);
        assert_eq!(offset_of!(FwdVmLayer, instruction_count), 2);

        assert_eq!(offset_of!(FwdVmDesc, arg_derived_e4), 0);
        assert_eq!(offset_of!(FwdVmDesc, source_base), 192);
        assert_eq!(offset_of!(FwdVmDesc, dst_base), 320);
        assert_eq!(offset_of!(FwdVmDesc, mapping_arena), 448);
        assert_eq!(offset_of!(FwdVmDesc, table), 472);
        assert_eq!(offset_of!(FwdVmDesc, mask), 480);
        assert_eq!(offset_of!(FwdVmDesc, source_stride_bytes), 488);
        assert_eq!(offset_of!(FwdVmDesc, dst_stride_bytes), 552);
        assert_eq!(offset_of!(FwdVmDesc, consts), 616);
        assert_eq!(offset_of!(FwdVmDesc, table_len), 872);
        assert_eq!(offset_of!(FwdVmDesc, descs), 876);
        assert_eq!(offset_of!(FwdVmDesc, count), 2_356);
        assert_eq!(offset_of!(FwdVmDesc, layer_count), 2_360);
        assert_eq!(offset_of!(FwdVmDesc, layers), 2_364);
        assert_eq!(offset_of!(FwdVmDesc, program), 2_396);
        assert_eq!(size_of::<FwdVmDesc>(), 26_976);
        assert_eq!(align_of::<FwdVmDesc>(), 16);
    }

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
            (SD_INITS_TOP_BITS, 0, 39, 0),
            (
                SD_VIRTUAL,
                ARENA_TIMESTAMP,
                u16::MAX,
                VKIND_INITS_AND_TEARDOWNS_LOW,
            ),
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
    fn decoder_descriptor_carries_its_const_derived_e4_slot_in_vkind() {
        for slot in 0..CONST_DERIVED_E4_CAP as u32 {
            assert_eq!(
                unpack_desc(pack_desc(SD_DECODER, 0, 17, slot)),
                (3, 0, 17, slot)
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
        // Raw shift (not pack_desc): DESC_VKIND_MASK (0x7) is outside
        // pack_desc's (2..=5) range check.
        let vkind = DESC_VKIND_MASK << DESC_VKIND_SHIFT;
        assert_eq!(kind & arena, 0);
        assert_eq!((kind | arena) & set_index, 0);
        assert_eq!((kind | arena | set_index) & vkind, 0);
        assert_eq!(
            kind | arena | set_index | vkind,
            0x00ff_ffff,
            "rsvd bits [24..32) must stay zero"
        );
    }

    #[test]
    #[should_panic(expected = "desc kind")]
    fn pack_desc_rejects_out_of_range_kind() {
        pack_desc(SD_INITS_TOP_BITS + 1, 0, 0, 0);
    }

    #[test]
    fn vkind_codes_match_gpu_gkr_compiler_wire_codes() {
        // `virtual_setup_kind_code` returns the `KIND_ORDER` index (0..3);
        // the packed-desc `vkind` field now stores the native
        // `gkr_base_source_kind` value verbatim (2..5), i.e. index + 2.
        use gkr_eval_ir::VirtualSetupKind::*;
        use gpu_gkr_compiler::virtual_setup_kind_code;
        assert_eq!(
            virtual_setup_kind_code(&RangeCheck16Bits) + 2,
            VKIND_RANGE_CHECK_16_BITS
        );
        assert_eq!(
            virtual_setup_kind_code(&RangeCheckTimestamp) + 2,
            VKIND_RANGE_CHECK_TIMESTAMP
        );
        assert_eq!(
            virtual_setup_kind_code(&InitsAndTeardownsLow) + 2,
            VKIND_INITS_AND_TEARDOWNS_LOW
        );
        assert_eq!(
            virtual_setup_kind_code(&InitsAndTeardownsHigh) + 2,
            VKIND_INITS_AND_TEARDOWNS_HIGH
        );
    }
}
