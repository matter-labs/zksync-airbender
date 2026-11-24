use crate::upstream::PR;

pub(crate) use crate::forward::vm::desc::{
    FwdVmLayer, ARG_DERIVED_E4_CAP, CONST_DERIVED_E4_CAP, DESC_CAP, DST_SLOT_COUNT,
    FUSED_REDUCTION_ROUNDS, LAYER_CAP, MAPPING_ARENA_COUNT, PROGRAM_CAP, REDUCTION_PAIR_CAP,
    SOURCE_WINDOW_COUNT,
};
pub const PR_FWD_VM_BUCKETS: u32 = 4;
pub const PR_FWD_VM_CONST_CAP: usize = 64;
pub(crate) const CONST_CAP: usize = PR_FWD_VM_CONST_CAP;

pub(crate) type FwdVmReductionPair = crate::forward::vm::desc::FwdVmReductionPair<PR>;

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct FwdVmDesc {
    pub arg_derived: *const PR,
    pub const_derived: *const PR,
    pub source_base: [*mut u8; SOURCE_WINDOW_COUNT],
    pub dst_base: [*mut u8; DST_SLOT_COUNT],
    pub mapping_arena: [*const u32; MAPPING_ARENA_COUNT],
    pub table: *const PR,
    pub mask: *const PR,
    pub decoder_mapping: *const u32,
    pub source_stride_bytes: [u32; SOURCE_WINDOW_COUNT],
    pub dst_stride_bytes: [u32; DST_SLOT_COUNT],
    pub consts: [PR; CONST_CAP],
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

const _: () = {
    use core::mem::{align_of, offset_of, size_of};
    assert!(size_of::<FwdVmDesc>() == 28_272);
    assert!(align_of::<FwdVmDesc>() == 16);
    assert!(offset_of!(FwdVmDesc, consts) == 448);
    assert!(offset_of!(FwdVmDesc, reduction_pairs) == 3000);
    assert!(offset_of!(FwdVmDesc, program) == 3680);
    assert!(offset_of!(FwdVmDesc, temporary_source_mask) == 28_256);
    assert!(offset_of!(FwdVmDesc, temporary_dst_mask) == 28_260);
    assert!(size_of::<FwdVmReductionPair>() == 136);
    assert!(size_of::<FwdVmDesc>() <= 32_764);
};
