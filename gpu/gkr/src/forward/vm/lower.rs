//! Field-specific assembly of the unchanged forward VM descriptor ABI.
use super::desc::{FwdVmDesc, MAPPING_ARENA_COUNT};
use crate::forward::vm::lower_common;
use crate::upstream::{ChallengeRef, GKRAddress};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::CompiledLayer;
pub(crate) use lower_common::{read_place_to_gkr_address, ResolvedColumn};

#[derive(Clone, Copy, Debug)]
pub(crate) struct FwdVmInputs<'a> {
    pub mapping_arena: [*const u32; MAPPING_ARENA_COUNT],
    pub decoder_mapping_col: Option<u16>,
    pub table: *const E4,
    pub table_len: u32,
    pub count: u32,
    pub inits_and_teardowns_top_bits: &'a [u32],
}

pub(crate) struct LoweredFwdVm {
    pub desc: FwdVmDesc,
    pub lookup_additive_slot: Option<usize>,
    pub decoder_fill_slot: Option<usize>,
    pub setup_fill_slot: Option<usize>,
}

pub(crate) fn lower_desc(
    layers: &[CompiledLayer],
    header: &FwdVmInputs<'_>,
    resolve_column: &dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
    challenge: &dyn Fn(&ChallengeRef) -> E4,
) -> LoweredFwdVm {
    let common_header = lower_common::FwdVmInputs {
        mapping_arena: header.mapping_arena,
        decoder_mapping_col: header.decoder_mapping_col,
        table: header.table,
        decoder_mapping: std::ptr::null(),
        table_len: header.table_len,
        count: header.count,
        inits_and_teardowns_top_bits: header.inits_and_teardowns_top_bits,
    };
    let lowered = lower_common::lower_desc::<BF>(layers, &common_header, resolve_column, challenge);
    let d = lowered.desc;
    let mut desc: FwdVmDesc = unsafe { std::mem::zeroed() };
    desc.source_base = d.source_base;
    desc.dst_base = d.dst_base;
    desc.mapping_arena = d.mapping_arena;
    desc.table = d.table;
    desc.mask = d.mask;
    desc.source_stride_bytes = d.source_stride_bytes;
    desc.dst_stride_bytes = d.dst_stride_bytes;
    desc.consts = d.consts;
    desc.table_len = d.table_len;
    desc.descs = d.descs;
    desc.count = d.count;
    desc.layer_count = d.layer_count;
    desc.layers = d.layers;
    desc.program = d.program;
    desc.arg_derived_e4 = d.arg_derived_e4;
    LoweredFwdVm {
        desc,
        lookup_additive_slot: lowered.lookup_additive_slot,
        decoder_fill_slot: lowered.decoder_fill_slot,
        setup_fill_slot: lowered.setup_fill_slot,
    }
}
