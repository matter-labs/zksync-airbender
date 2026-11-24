//! BabyBear forward VM descriptor, filled from the field-generic lowering in `lower_common`.
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::CompiledLayer;
pub(crate) use lower_common::ResolvedColumn;

use crate::baby_bear::forward::vm::desc::FwdVmDesc;
use crate::forward::vm::lower_common;
use crate::forward::vm::lower_common::FwdVmInputs;
use crate::upstream::ChallengeRef;
use crate::upstream::GKRAddress;

pub(crate) struct LoweredFwdVm {
    pub desc: FwdVmDesc,
    pub lookup_additive_slot: Option<usize>,
    pub decoder_fill_slot: Option<usize>,
    pub setup_fill_slot: Option<usize>,
}

pub(crate) fn lower_desc(
    layers: &[CompiledLayer],
    header: &FwdVmInputs<'_, E4>,
    resolve_column: &dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
    challenge: &dyn Fn(&ChallengeRef) -> E4,
) -> LoweredFwdVm {
    let lowered = lower_common::lower_desc::<BF>(layers, header, resolve_column, challenge);
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
