//! Rust half of the forward VM descriptor ABI.

use crate::forward::vm::desc::*;

#[cfg(test)]
use crate::forward::vm::desc::unpack_desc;

use gpu_core::primitives::field::{BF, E4};

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
    pub reduction_pair_count: u32,
    pub reduction_pairs: [FwdVmReductionPair; REDUCTION_PAIR_CAP],
    pub program: [u16; PROGRAM_CAP],
    pub temporary_source_mask: u32,
    pub temporary_dst_mask: u32,
}

/// ABI size guards, paired with the CUDA `static_assert`s in `fwd_vm.cuh`.
const _: () = {
    assert!(core::mem::size_of::<FwdVmLayer>() == 4);
    assert!(core::mem::size_of::<FwdVmReductionPair>() == 136);
    assert!(core::mem::align_of::<FwdVmReductionPair>() == 8);
    assert!(core::mem::size_of::<FwdVmDesc>() == 27_664);
    assert!(core::mem::offset_of!(FwdVmDesc, temporary_source_mask) == 27_656);
    assert!(core::mem::offset_of!(FwdVmDesc, temporary_dst_mask) == 27_660);
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

        assert_eq!(size_of::<FwdVmReductionPair>(), 136);
        assert_eq!(align_of::<FwdVmReductionPair>(), 8);
        assert_eq!(offset_of!(FwdVmReductionPair, input), 0);
        assert_eq!(offset_of!(FwdVmReductionPair, round_outputs), 16);
        assert_eq!(offset_of!(FwdVmReductionPair, kind), 128);
        assert_eq!(offset_of!(FwdVmReductionPair, reserved), 132);

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
        assert_eq!(offset_of!(FwdVmDesc, reduction_pair_count), 2_396);
        assert_eq!(offset_of!(FwdVmDesc, reduction_pairs), 2_400);
        assert_eq!(offset_of!(FwdVmDesc, program), 3_080);
        assert_eq!(size_of::<FwdVmDesc>(), 27_664);
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
    fn setup_descriptor_carries_its_const_derived_e4_slot_in_vkind() {
        for slot in 0..CONST_DERIVED_E4_CAP as u32 {
            assert_eq!(
                unpack_desc(pack_desc(SD_SETUP, 0, 0, slot)),
                (SD_SETUP, 0, 0, slot)
            );
        }
    }

    #[test]
    #[should_panic(expected = "const-derived-E4 slot 8 out of range")]
    fn setup_descriptor_rejects_out_of_range_const_derived_e4_slot() {
        pack_desc(SD_SETUP, 0, 0, CONST_DERIVED_E4_CAP as u32);
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
