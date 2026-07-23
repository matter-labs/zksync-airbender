use std::collections::{BTreeMap, BTreeSet};
use std::ptr;

use era_cudart::result::CudaResult;
use gkr_eval_isa::bwd::distill::DistilledLayer;
use gkr_eval_isa::bwd::fragment::MergedRecipe;
use gkr_eval_isa::bwd::source::{BwdSpecial, OriginLeaf};
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::eval_plan::backward_search::{
    problem::build_backward_search_problem, BackwardSearchError, StaticMaterialization,
};
use gkr_eval_isa::eval_plan::CompiledBackwardEvaluation;
use gkr_eval_isa::fwd::encode::{decode, encode};
use gkr_eval_isa::fwd::error::EncodeError;
use gkr_eval_isa::fwd::isa::{
    DstLine, Instr, LdcSub, OperandField, OperandLine, Program, MAX_SOURCE_WINDOWS,
    SOURCE_WINDOW_COLUMNS,
};
use gkr_eval_isa::fwd::source::virtual_setup_kind_code;

use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::flat::FLAT_CONST_MAX;
use crate::prover::gkr::backward::GkrEqSizes;
use crate::prover::gkr::forward::vm::lower::{read_place_to_gkr_address, ResolvedColumn};
use crate::prover::ProverContext;
use crate::upstream::{ChallengeRef, Field, GKRAddress, PrimeField};
#[cfg(all(test, feature = "bench"))]
use cs::gkr_compiler::dag_ir::DagLayer;

use super::desc::{
    BwdVmDesc, BwdVmSourceWindow, BwdVmSpecial, SpecialLoweringError, BWD_VM_ARG_DERIVED_E4_CAP,
    BWD_VM_BF_CONSTANT_CAP, BWD_VM_CELL_CAP, BWD_VM_COEFFICIENT_CAP, BWD_VM_CONST_DERIVED_E4_CAP,
    BWD_VM_PROGRAM_CAP, BWD_VM_SOURCE_READ_BASE, BWD_VM_SOURCE_READ_EXT, BWD_VM_SOURCE_VIRTUAL,
    BWD_VM_SOURCE_WINDOW_CAP, BWD_VM_SPECIAL_CAP, BWD_VM_VIRTUAL_MATERIALIZE_DEPTH,
};

pub(crate) struct BwdVmRoundBinding<'a> {
    pub round: u8,
    pub rows: u32,
    pub round_challenges: &'a [E4],
    pub sources: &'a [ResolvedBwdSourceWindow],
    pub virtual_sources: &'a [ResolvedBwdVirtualSource],
    pub resolve_source: &'a dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
    pub eq_low: *const E4,
    pub eq_sizes: GkrEqSizes,
    pub contributions: *mut E4,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedBwdSourceWindow {
    pub logical_window: u8,
    pub logical_column: u8,
    pub read: ResolvedColumn,
    pub publish: Option<ResolvedColumn>,
    pub backing_depth: u8,
    pub target_depth: u8,
    pub materialize: bool,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedBwdVirtualSource {
    pub desc: u16,
    pub read: Option<ResolvedColumn>,
    pub publish: Option<ResolvedColumn>,
    pub backing_depth: u8,
    pub target_depth: u8,
    pub materialize: bool,
}

pub(crate) struct BwdVmSetup {
    pub desc: BwdVmDesc,
    pub const_derived_e4: Vec<E4>,
    pub coefficients: Vec<E4>,
}

/// Rebuild the static source-round projection whose certificate was checked
/// while loading an add/sub artifact case. The projection is independent of
/// the paging decisions in the compiled candidate; callers must still map its
/// states and `store_for_next_round` bit literally into runtime storage.
#[cfg(all(test, feature = "bench"))]
pub(crate) fn artifact_static_materialization(
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
) -> Result<StaticMaterialization, BackwardSearchError> {
    let (_, problem) =
        build_backward_search_problem(canonical, distilled, trace_len, budget_cells)?;
    let problem = problem.ok_or(BackwardSearchError::SearchDriverFailure {
        reason: "artifact-certified backward problem is infeasible",
    })?;
    Ok(problem.materialization)
}

impl BwdVmSetup {
    /// Upload the two host-evaluated banks consumed by the backward VM. Both
    /// copies are enqueued on `exec_stream`, so a following validate or release
    /// launch observes this setup without a host synchronization. Unused slots
    /// are cleared to keep relaunches independent of the previous setup.
    pub(crate) fn upload_constant_banks(&self, context: &ProverContext) -> CudaResult<()> {
        assert_eq!(self.coefficients.len(), self.desc.n_coefficients as usize);
        assert_eq!(
            self.const_derived_e4.len(),
            self.desc.n_const_derived_e4 as usize
        );
        assert!(self.coefficients.len() <= BWD_VM_COEFFICIENT_CAP);
        assert!(self.const_derived_e4.len() <= BWD_VM_CONST_DERIVED_E4_CAP);

        let coefficients: [E4; FLAT_CONST_MAX] =
            core::array::from_fn(|index| self.coefficients.get(index).copied().unwrap_or(E4::ZERO));
        let const_derived_e4: [E4; BWD_VM_CONST_DERIVED_E4_CAP] = core::array::from_fn(|index| {
            self.const_derived_e4
                .get(index)
                .copied()
                .unwrap_or(E4::ZERO)
        });
        // SAFETY: both Rust statics are stubs for the exact CUDA __constant__
        // arrays with matching element counts/layout. Pageable sources are
        // staged by cudaMemcpyToSymbolAsync before this function returns; the
        // device copies remain ordered before the caller's next exec-stream
        // launch.
        unsafe {
            crate::primitives::utils::memcpy_to_symbol_async(
                &super::ab_gkr_flat_coefficients,
                &coefficients,
                context.get_exec_stream(),
            )?;
            crate::primitives::utils::memcpy_to_symbol_async(
                &super::ab_gkr_fwd_vm_const_derived_e4,
                &const_derived_e4,
                context.get_exec_stream(),
            )
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BwdVmLowerError {
    InvalidInputEncoding,
    InputProgramMismatch,
    Encode(EncodeError),
    OutputRoundTripMismatch,
    UnmappedSource {
        window: u8,
        column: u8,
    },
    MissingSourceBinding {
        window: u8,
        column: u8,
    },
    DuplicateSourceBinding {
        window: u8,
        column: u8,
    },
    UnknownSourceBinding {
        window: u8,
        column: u8,
    },
    ConflictingSourceField {
        window: u8,
        column: u8,
    },
    SourceFieldMismatch {
        window: u8,
        column: u8,
        expect_e4: bool,
        got_e4: bool,
    },
    MissingResolvedSource {
        window: u8,
        column: u8,
    },
    SourceIdentityMismatch {
        window: u8,
        column: u8,
    },
    NullSourceGeometry {
        window: u8,
        column: u8,
    },
    SourceColumnOffStride {
        window: u8,
        column: u8,
    },
    SourceColumnRemapCollision {
        window: u8,
        column: u8,
        matrix_column: usize,
    },
    SourceColumnOverflow {
        window: u8,
        column: u8,
        offset: usize,
    },
    MissingPublishBinding {
        window: u8,
        column: u8,
    },
    UnexpectedPublishBinding {
        window: u8,
        column: u8,
    },
    PublishFieldMismatch {
        window: u8,
        column: u8,
        expect_e4: bool,
        got_e4: bool,
    },
    NullPublishGeometry {
        window: u8,
        column: u8,
    },
    InvalidDepths {
        window: u8,
        column: u8,
        backing_depth: u8,
        target_depth: u8,
        round: u8,
    },
    PlainSourceDepthMismatch {
        window: u8,
        column: u8,
    },
    MissingVirtualSourceBinding {
        desc: u16,
    },
    DuplicateVirtualSourceBinding {
        desc: u16,
    },
    UnknownVirtualSourceBinding {
        desc: u16,
    },
    VirtualSourceFieldMismatch {
        desc: u16,
    },
    MissingVirtualReadBinding {
        desc: u16,
    },
    UnexpectedVirtualReadBinding {
        desc: u16,
    },
    MissingVirtualPublishBinding {
        desc: u16,
    },
    UnexpectedVirtualPublishBinding {
        desc: u16,
    },
    InvalidVirtualDepths {
        desc: u16,
        backing_depth: u8,
        target_depth: u8,
        round: u8,
    },
    InvalidVirtualMaterialization {
        desc: u16,
        target_depth: u8,
        materialize: bool,
    },
    VirtualSourceGeometryMismatch {
        desc: u16,
    },
    VirtualSourceColumnMismatch {
        desc: u16,
        expected: u8,
        actual: usize,
    },
    UnsafeVirtualReadPublishAlias {
        desc: u16,
    },
    UnmappedVirtualSource {
        desc: u16,
    },
    RoundChallengesTooShort {
        required: usize,
        actual: usize,
    },
    UnsafeReadPublishAlias {
        window: u8,
        column: u8,
    },
    UnsafePublishAlias {
        window: u8,
        column: u8,
        other_window: u8,
        other_column: u8,
    },
    InvalidFoldDescriptor {
        window: u8,
        column: u8,
        desc: u16,
    },
    MissingSpecial {
        desc: u16,
    },
    ReadFoldSpecial {
        desc: u16,
    },
    InvalidCoefficientFragment {
        desc: u16,
        fragment: u32,
    },
    Special(SpecialLoweringError),
    Capacity {
        field: &'static str,
        actual: usize,
        cap: usize,
    },
}

pub(crate) fn lower_bwd_vm(
    compiled: &CompiledBackwardEvaluation,
    distilled: &DistilledLayer,
    runtime: &BwdVmRoundBinding<'_>,
    evaluate_derived: &impl Fn(&ChallengeRef) -> E4,
    evaluate_recipe: &impl Fn(&MergedRecipe) -> E4,
) -> Result<BwdVmSetup, BwdVmLowerError> {
    let active_round_challenges = runtime.round as usize;
    if runtime.round_challenges.len() < active_round_challenges {
        return Err(BwdVmLowerError::RoundChallengesTooShort {
            required: active_round_challenges,
            actual: runtime.round_challenges.len(),
        });
    }
    let input = decode(&compiled.encoded).map_err(|_| BwdVmLowerError::InvalidInputEncoding)?;
    if input != compiled.compiled.program {
        return Err(BwdVmLowerError::InputProgramMismatch);
    }

    let mut source_geometry = lower_source_geometry(compiled, runtime, &input)?;
    let virtual_geometry = lower_virtual_source_geometry(
        compiled,
        runtime,
        &input,
        source_geometry.windows.len() as u8,
    )?;
    if let Some(window) = virtual_geometry.window {
        source_geometry.windows.push(window);
    }
    check_cap(
        "source_windows",
        source_geometry.windows.len(),
        BWD_VM_SOURCE_WINDOW_CAP,
    )?;
    let special_geometry = lower_specials(
        compiled,
        distilled,
        &input,
        &virtual_geometry.remap,
        evaluate_recipe,
    )?;
    let rewritten = rewrite_program(
        &input,
        &source_geometry.remap,
        &virtual_geometry.remap,
        &special_geometry.remap,
    )?;
    let encoded = encode(&rewritten).map_err(BwdVmLowerError::Encode)?;
    if decode(&encoded).ok().as_ref() != Some(&rewritten) {
        return Err(BwdVmLowerError::OutputRoundTripMismatch);
    }
    check_cap("program_lanes", encoded.len(), BWD_VM_PROGRAM_CAP)?;

    // SAFETY: all-zero bytes are a valid descriptor: it contains POD scalars,
    // arrays, and nullable raw pointers. Every live range is filled below.
    let mut desc: BwdVmDesc = unsafe { core::mem::zeroed() };
    desc.source_windows[..source_geometry.windows.len()].copy_from_slice(&source_geometry.windows);
    desc.specials[..special_geometry.specials.len()].copy_from_slice(&special_geometry.specials);
    desc.program[..encoded.len()].copy_from_slice(&encoded);

    let consts = compiled.compiled.consts.values();
    check_cap("bf_constants", consts.len(), BWD_VM_BF_CONSTANT_CAP)?;
    for (dst, &value) in desc.bf_constants.iter_mut().zip(consts) {
        *dst = BF::from_u32_with_reduction(value);
    }

    let n_arg = derived_e4_bank_len(compiled, LdcSub::ArgDerivedE4, BWD_VM_ARG_DERIVED_E4_CAP);
    check_cap("arg_derived_e4", n_arg, BWD_VM_ARG_DERIVED_E4_CAP)?;
    for index in 0..n_arg {
        let reference = compiled
            .compiled
            .derived_e4
            .get(LdcSub::ArgDerivedE4, index as u16)
            .expect("derived bank is dense below its measured length");
        desc.arg_derived_e4[index] = evaluate_derived(reference);
    }

    let n_const = derived_e4_bank_len(
        compiled,
        LdcSub::ConstDerivedE4,
        BWD_VM_CONST_DERIVED_E4_CAP,
    );
    check_cap("const_derived_e4", n_const, BWD_VM_CONST_DERIVED_E4_CAP)?;
    let const_derived_e4 = (0..n_const)
        .map(|index| {
            evaluate_derived(
                compiled
                    .compiled
                    .derived_e4
                    .get(LdcSub::ConstDerivedE4, index as u16)
                    .expect("derived bank is dense below its measured length"),
            )
        })
        .collect();

    let cell_count = program_cell_count(&rewritten);
    check_cap("cell_count", cell_count, BWD_VM_CELL_CAP)?;
    check_cap(
        "round_challenges",
        active_round_challenges,
        u32::MAX as usize,
    )?;

    desc.round_challenges = runtime.round_challenges.as_ptr();
    desc.eq_low = runtime.eq_low;
    desc.contributions = runtime.contributions;
    desc.eq_sizes = runtime.eq_sizes;
    desc.n_instr = rewritten.instrs.len() as u32;
    desc.program_lanes = encoded.len() as u32;
    desc.n_source_windows = source_geometry.windows.len() as u32;
    desc.n_specials = special_geometry.specials.len() as u32;
    desc.n_coefficients = special_geometry.coefficients.len() as u32;
    desc.n_bf_constants = consts.len() as u32;
    desc.n_arg_derived_e4 = n_arg as u32;
    desc.n_const_derived_e4 = n_const as u32;
    // This count is also the procedural Ext VirtualSetup fold depth in CUDA.
    // The backing slice may contain later transcript challenges, but only the
    // active prefix is semantically visible in this round.
    desc.n_round_challenges = runtime.round.into();
    desc.logical_rows = runtime.rows;
    desc.cell_count = cell_count as u32;

    Ok(BwdVmSetup {
        desc,
        const_derived_e4,
        coefficients: special_geometry.coefficients,
    })
}

fn check_cap(field: &'static str, actual: usize, cap: usize) -> Result<(), BwdVmLowerError> {
    if actual > cap {
        return Err(BwdVmLowerError::Capacity { field, actual, cap });
    }
    Ok(())
}

fn source_fields(program: &Program) -> Result<BTreeMap<(u8, u8), OperandField>, BwdVmLowerError> {
    let mut fields = BTreeMap::new();
    let mut conflict = None;
    visit_operands(program, |operand, field| {
        if let OperandLine::Source { window, column, .. } = *operand {
            let coordinate = (window, column);
            if fields
                .insert(coordinate, field)
                .is_some_and(|prior| prior != field)
            {
                conflict = Some(coordinate);
            }
        }
    });
    if let Some((window, column)) = conflict {
        return Err(BwdVmLowerError::ConflictingSourceField { window, column });
    }
    Ok(fields)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SourceGroupKey {
    read_base: usize,
    read_stride: u32,
    publish_base: usize,
    publish_stride: u32,
    publish_delta: i128,
    is_e4: bool,
    backing_depth: u8,
    target_depth: u8,
    materialize: bool,
}

struct SourceGroup {
    key: SourceGroupKey,
    entries: Vec<((u8, u8), usize, Option<usize>)>,
}

struct SourceGeometry {
    windows: Vec<BwdVmSourceWindow>,
    remap: BTreeMap<(u8, u8), (u8, u8)>,
}

fn lower_source_geometry(
    compiled: &CompiledBackwardEvaluation,
    runtime: &BwdVmRoundBinding<'_>,
    program: &Program,
) -> Result<SourceGeometry, BwdVmLowerError> {
    let source_fields = source_fields(program)?;
    let coordinates = source_fields.keys().copied().collect::<BTreeSet<_>>();
    let mut bindings = BTreeMap::<(u8, u8), &ResolvedBwdSourceWindow>::new();
    for binding in runtime.sources {
        let coordinate = (binding.logical_window, binding.logical_column);
        if !coordinates.contains(&coordinate) {
            return Err(BwdVmLowerError::UnknownSourceBinding {
                window: coordinate.0,
                column: coordinate.1,
            });
        }
        if bindings.insert(coordinate, binding).is_some() {
            return Err(BwdVmLowerError::DuplicateSourceBinding {
                window: coordinate.0,
                column: coordinate.1,
            });
        }
    }
    for &(window, column) in &coordinates {
        if !bindings.contains_key(&(window, column)) {
            return Err(BwdVmLowerError::MissingSourceBinding { window, column });
        }
    }

    let mut groups = Vec::<SourceGroup>::new();
    for &(window, column) in &coordinates {
        let binding = bindings
            .get(&(window, column))
            .copied()
            .ok_or(BwdVmLowerError::MissingSourceBinding { window, column })?;
        let place = compiled
            .compiled
            .source_windows
            .resolve_read_place(window, column)
            .ok_or(BwdVmLowerError::UnmappedSource { window, column })?;
        let fold_desc = compiled.compiled.source_windows.fold_desc(window, column);
        if let Some(desc) = fold_desc {
            match compiled.compiled.specials.get(desc) {
                Some(BwdSpecial::FoldSource {
                    origin: OriginLeaf::Read(expected),
                }) if *expected == place => {}
                _ => {
                    return Err(BwdVmLowerError::InvalidFoldDescriptor {
                        window,
                        column,
                        desc,
                    });
                }
            }
        }

        // A backward Ext FoldSource is evaluated as Ext even when its physical
        // origin is a base-field matrix. The instruction operand field is the
        // runtime backing contract; SourceWindowTable::source_field describes
        // only that origin matrix and would reject the required lifted backing.
        let expect_e4 = source_fields[&(window, column)] == OperandField::Ext;
        if binding.read.is_e4 != expect_e4 {
            return Err(BwdVmLowerError::SourceFieldMismatch {
                window,
                column,
                expect_e4,
                got_e4: binding.read.is_e4,
            });
        }
        validate_source_geometry(&binding.read, window, column)?;
        let expected_read = (runtime.resolve_source)(read_place_to_gkr_address(&place))
            .ok_or(BwdVmLowerError::MissingResolvedSource { window, column })?;
        validate_source_geometry(&expected_read, window, column)?;
        if !same_resolved_column(&binding.read, &expected_read) {
            return Err(BwdVmLowerError::SourceIdentityMismatch { window, column });
        }
        if binding.backing_depth > binding.target_depth || binding.target_depth != runtime.round {
            return Err(BwdVmLowerError::InvalidDepths {
                window,
                column,
                backing_depth: binding.backing_depth,
                target_depth: binding.target_depth,
                round: runtime.round,
            });
        }
        if fold_desc.is_none() && binding.backing_depth != binding.target_depth {
            return Err(BwdVmLowerError::PlainSourceDepthMismatch { window, column });
        }
        let required_challenges = binding.target_depth as usize;
        if runtime.round_challenges.len() < required_challenges {
            return Err(BwdVmLowerError::RoundChallengesTooShort {
                required: required_challenges,
                actual: runtime.round_challenges.len(),
            });
        }

        let read_column = matrix_column(&binding.read, window, column)?;
        let publish_column = match (binding.materialize, binding.publish.as_ref()) {
            (true, None) => {
                return Err(BwdVmLowerError::MissingPublishBinding { window, column });
            }
            (false, Some(_)) => {
                return Err(BwdVmLowerError::UnexpectedPublishBinding { window, column });
            }
            (_, publish) => publish
                .map(|publish| {
                    if publish.is_e4 != expect_e4 {
                        return Err(BwdVmLowerError::PublishFieldMismatch {
                            window,
                            column,
                            expect_e4,
                            got_e4: publish.is_e4,
                        });
                    }
                    validate_publish_geometry(publish, window, column)?;
                    matrix_column(publish, window, column)
                })
                .transpose()?,
        };
        let publish = binding.publish.as_ref();
        let key = SourceGroupKey {
            read_base: binding.read.matrix_base as usize,
            read_stride: binding.read.stride_bytes,
            publish_base: publish.map_or(0, |column| column.matrix_base as usize),
            publish_stride: publish.map_or(0, |column| column.stride_bytes),
            publish_delta: publish_column.map_or(0, |publish_column| {
                publish_column as i128 - read_column as i128
            }),
            is_e4: expect_e4,
            backing_depth: binding.backing_depth,
            target_depth: binding.target_depth,
            materialize: binding.materialize,
        };
        let group = if let Some(index) = groups.iter().position(|group| group.key == key) {
            index
        } else {
            groups.push(SourceGroup {
                key,
                entries: Vec::new(),
            });
            groups.len() - 1
        };
        groups[group]
            .entries
            .push(((window, column), read_column, publish_column));
    }

    // Materialization writes a complete target column on first access even
    // when the source is already at the target depth. Every publish therefore
    // must be disjoint from every read and from every other publish.
    let materialized = bindings
        .iter()
        .filter_map(|(&coordinate, binding)| {
            if binding.materialize {
                binding
                    .publish
                    .as_ref()
                    .map(|publish| (coordinate, publish))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    for &((window, column), publish) in &materialized {
        if bindings.values().any(|other| {
            byte_ranges_overlap(
                other.read.ptr,
                other.read.stride_bytes,
                publish.ptr,
                publish.stride_bytes,
            )
        }) {
            return Err(BwdVmLowerError::UnsafeReadPublishAlias { window, column });
        }
    }
    for (index, &((window, column), publish)) in materialized.iter().enumerate() {
        for &((other_window, other_column), other_publish) in &materialized[index + 1..] {
            if byte_ranges_overlap(
                publish.ptr,
                publish.stride_bytes,
                other_publish.ptr,
                other_publish.stride_bytes,
            ) {
                return Err(BwdVmLowerError::UnsafePublishAlias {
                    window,
                    column,
                    other_window,
                    other_column,
                });
            }
        }
    }

    check_cap(
        "encoded_source_windows",
        groups.len(),
        MAX_SOURCE_WINDOWS as usize,
    )?;
    check_cap("source_windows", groups.len(), BWD_VM_SOURCE_WINDOW_CAP)?;

    let mut windows = Vec::with_capacity(groups.len());
    let mut remap = BTreeMap::new();
    for (wire, mut group) in groups.into_iter().enumerate() {
        group
            .entries
            .sort_by_key(|(_, read_column, _)| *read_column);
        let first_read = group.entries[0].1;
        let first_publish = group.entries[0].2;
        let mut claimed = BTreeSet::new();
        for &((window, column), read_column, publish_column) in &group.entries {
            if !claimed.insert(read_column) {
                return Err(BwdVmLowerError::SourceColumnRemapCollision {
                    window,
                    column,
                    matrix_column: read_column,
                });
            }
            let offset = read_column - first_read;
            if offset >= SOURCE_WINDOW_COLUMNS as usize {
                return Err(BwdVmLowerError::SourceColumnOverflow {
                    window,
                    column,
                    offset,
                });
            }
            if let (Some(publish_column), Some(first_publish)) = (publish_column, first_publish) {
                debug_assert_eq!(publish_column - first_publish, offset);
            }
            remap.insert((window, column), (wire as u8, offset as u8));
        }

        let read_base = checked_column_ptr(group.key.read_base, first_read, group.key.read_stride)
            .ok_or_else(|| {
                let ((window, column), _, _) = group.entries[0];
                BwdVmLowerError::SourceColumnOffStride { window, column }
            })?;
        let publish_base = match first_publish {
            Some(first_publish) => checked_column_ptr(
                group.key.publish_base,
                first_publish,
                group.key.publish_stride,
            )
            .ok_or_else(|| {
                let ((window, column), _, _) = group.entries[0];
                BwdVmLowerError::SourceColumnOffStride { window, column }
            })? as *mut u8,
            None => ptr::null_mut(),
        };
        windows.push(BwdVmSourceWindow {
            read_base: read_base as *const u8,
            publish_base,
            read_stride_bytes: group.key.read_stride,
            publish_stride_bytes: group.key.publish_stride,
            backing_depth: group.key.backing_depth,
            target_depth: group.key.target_depth,
            source_kind: if group.key.is_e4 {
                BWD_VM_SOURCE_READ_EXT
            } else {
                BWD_VM_SOURCE_READ_BASE
            },
            materialize: u8::from(group.key.materialize),
        });
    }

    Ok(SourceGeometry { windows, remap })
}

struct VirtualSourceGeometry {
    window: Option<BwdVmSourceWindow>,
    remap: BTreeMap<u16, (u8, u8)>,
}

fn lower_virtual_source_geometry(
    compiled: &CompiledBackwardEvaluation,
    runtime: &BwdVmRoundBinding<'_>,
    program: &Program,
    wire_window: u8,
) -> Result<VirtualSourceGeometry, BwdVmLowerError> {
    let mut referenced = BTreeMap::<u16, u8>::new();
    let mut field_error = None;
    visit_operands(program, |operand, field| {
        let OperandLine::Special { desc } = *operand else {
            return;
        };
        let Some(BwdSpecial::FoldSource {
            origin: OriginLeaf::VirtualSetup { kind },
        }) = compiled.compiled.specials.get(desc)
        else {
            return;
        };
        if field != OperandField::Ext {
            field_error = Some(desc);
            return;
        }
        referenced.insert(desc, virtual_setup_kind_code(kind) as u8);
    });
    if let Some(desc) = field_error {
        return Err(BwdVmLowerError::VirtualSourceFieldMismatch { desc });
    }

    let mut bindings = BTreeMap::<u16, &ResolvedBwdVirtualSource>::new();
    for binding in runtime.virtual_sources {
        if !referenced.contains_key(&binding.desc) {
            return Err(BwdVmLowerError::UnknownVirtualSourceBinding { desc: binding.desc });
        }
        if bindings.insert(binding.desc, binding).is_some() {
            return Err(BwdVmLowerError::DuplicateVirtualSourceBinding { desc: binding.desc });
        }
    }
    for &desc in referenced.keys() {
        if !bindings.contains_key(&desc) {
            return Err(BwdVmLowerError::MissingVirtualSourceBinding { desc });
        }
    }
    if referenced.is_empty() {
        return Ok(VirtualSourceGeometry {
            window: None,
            remap: BTreeMap::new(),
        });
    }

    let mut common_depths = None;
    let mut read_geometry = None;
    let mut publish_geometry = None;
    let mut read_columns = Vec::new();
    let mut publish_columns = Vec::new();
    let mut remap = BTreeMap::new();
    let mut claimed_columns = BTreeSet::new();

    for (&desc, &column) in &referenced {
        let binding = bindings[&desc];
        if binding.target_depth != runtime.round
            || !((binding.backing_depth == 0
                && binding.target_depth <= BWD_VM_VIRTUAL_MATERIALIZE_DEPTH)
                || (binding.backing_depth >= BWD_VM_VIRTUAL_MATERIALIZE_DEPTH
                    && binding.backing_depth.checked_add(1) == Some(binding.target_depth)))
        {
            return Err(BwdVmLowerError::InvalidVirtualDepths {
                desc,
                backing_depth: binding.backing_depth,
                target_depth: binding.target_depth,
                round: runtime.round,
            });
        }
        let expected_materialize = binding.target_depth >= BWD_VM_VIRTUAL_MATERIALIZE_DEPTH;
        if binding.materialize != expected_materialize {
            return Err(BwdVmLowerError::InvalidVirtualMaterialization {
                desc,
                target_depth: binding.target_depth,
                materialize: binding.materialize,
            });
        }
        let depths = (
            binding.backing_depth,
            binding.target_depth,
            binding.materialize,
        );
        if common_depths.is_some_and(|common| common != depths) {
            return Err(BwdVmLowerError::VirtualSourceGeometryMismatch { desc });
        }
        common_depths = Some(depths);

        match (binding.backing_depth, binding.read.as_ref()) {
            (0, Some(_)) => {
                return Err(BwdVmLowerError::UnexpectedVirtualReadBinding { desc });
            }
            (0, None) => {}
            (_, None) => {
                return Err(BwdVmLowerError::MissingVirtualReadBinding { desc });
            }
            (_, Some(read)) => {
                if !read.is_e4 {
                    return Err(BwdVmLowerError::VirtualSourceFieldMismatch { desc });
                }
                validate_source_geometry(read, wire_window, column)?;
                let actual = matrix_column(read, wire_window, column)?;
                if actual != column as usize {
                    return Err(BwdVmLowerError::VirtualSourceColumnMismatch {
                        desc,
                        expected: column,
                        actual,
                    });
                }
                let geometry = (read.matrix_base as usize, read.stride_bytes);
                if read_geometry.is_some_and(|common| common != geometry) {
                    return Err(BwdVmLowerError::VirtualSourceGeometryMismatch { desc });
                }
                read_geometry = Some(geometry);
                read_columns.push((desc, read));
            }
        }

        match (binding.materialize, binding.publish.as_ref()) {
            (true, None) => {
                return Err(BwdVmLowerError::MissingVirtualPublishBinding { desc });
            }
            (false, Some(_)) => {
                return Err(BwdVmLowerError::UnexpectedVirtualPublishBinding { desc });
            }
            (false, None) => {}
            (true, Some(publish)) => {
                if !publish.is_e4 {
                    return Err(BwdVmLowerError::VirtualSourceFieldMismatch { desc });
                }
                validate_publish_geometry(publish, wire_window, column)?;
                let actual = matrix_column(publish, wire_window, column)?;
                if actual != column as usize {
                    return Err(BwdVmLowerError::VirtualSourceColumnMismatch {
                        desc,
                        expected: column,
                        actual,
                    });
                }
                let geometry = (publish.matrix_base as usize, publish.stride_bytes);
                if publish_geometry.is_some_and(|common| common != geometry) {
                    return Err(BwdVmLowerError::VirtualSourceGeometryMismatch { desc });
                }
                publish_geometry = Some(geometry);
                publish_columns.push((desc, publish));
            }
        }

        if !claimed_columns.insert(column) {
            return Err(BwdVmLowerError::VirtualSourceGeometryMismatch { desc });
        }
        remap.insert(desc, (wire_window, column));
    }

    for &(desc, publish) in &publish_columns {
        if read_columns.iter().any(|&(_, read)| {
            byte_ranges_overlap(
                read.ptr,
                read.stride_bytes,
                publish.ptr,
                publish.stride_bytes,
            )
        }) {
            return Err(BwdVmLowerError::UnsafeVirtualReadPublishAlias { desc });
        }
    }

    let (backing_depth, target_depth, materialize) =
        common_depths.expect("a referenced virtual source has runtime geometry");
    let (read_base, read_stride_bytes) = read_geometry.unwrap_or((0, 0));
    let (publish_base, publish_stride_bytes) = publish_geometry.unwrap_or((0, 0));
    let window = BwdVmSourceWindow {
        read_base: read_base as *const u8,
        publish_base: publish_base as *mut u8,
        read_stride_bytes,
        publish_stride_bytes,
        backing_depth,
        target_depth,
        source_kind: BWD_VM_SOURCE_VIRTUAL,
        materialize: u8::from(materialize),
    };
    Ok(VirtualSourceGeometry {
        window: Some(window),
        remap,
    })
}

fn matrix_column(
    resolved: &ResolvedColumn,
    window: u8,
    column: u8,
) -> Result<usize, BwdVmLowerError> {
    if resolved.stride_bytes == 0 {
        return Err(BwdVmLowerError::SourceColumnOffStride { window, column });
    }
    let offset = (resolved.ptr as usize)
        .checked_sub(resolved.matrix_base as usize)
        .ok_or(BwdVmLowerError::SourceColumnOffStride { window, column })?;
    if offset % resolved.stride_bytes as usize != 0 {
        return Err(BwdVmLowerError::SourceColumnOffStride { window, column });
    }
    Ok(offset / resolved.stride_bytes as usize)
}

fn validate_source_geometry(
    resolved: &ResolvedColumn,
    window: u8,
    column: u8,
) -> Result<(), BwdVmLowerError> {
    if resolved.ptr.is_null() || resolved.matrix_base.is_null() {
        return Err(BwdVmLowerError::NullSourceGeometry { window, column });
    }
    Ok(())
}

fn validate_publish_geometry(
    resolved: &ResolvedColumn,
    window: u8,
    column: u8,
) -> Result<(), BwdVmLowerError> {
    if resolved.ptr.is_null() || resolved.matrix_base.is_null() {
        return Err(BwdVmLowerError::NullPublishGeometry { window, column });
    }
    Ok(())
}

fn same_resolved_column(lhs: &ResolvedColumn, rhs: &ResolvedColumn) -> bool {
    lhs.is_e4 == rhs.is_e4
        && lhs.ptr == rhs.ptr
        && lhs.matrix_base == rhs.matrix_base
        && lhs.stride_bytes == rhs.stride_bytes
}

fn checked_column_ptr(base: usize, column: usize, stride: u32) -> Option<usize> {
    column
        .checked_mul(stride as usize)
        .and_then(|offset| base.checked_add(offset))
}

fn byte_ranges_overlap(a: *const u8, a_len: u32, b: *const u8, b_len: u32) -> bool {
    let a_start = a as usize;
    let b_start = b as usize;
    let a_end = a_start.checked_add(a_len as usize).unwrap_or(usize::MAX);
    let b_end = b_start.checked_add(b_len as usize).unwrap_or(usize::MAX);
    a_start < b_end && b_start < a_end
}

struct SpecialGeometry {
    specials: Vec<BwdVmSpecial>,
    coefficients: Vec<E4>,
    remap: BTreeMap<u16, u16>,
}

fn lower_specials(
    compiled: &CompiledBackwardEvaluation,
    distilled: &DistilledLayer,
    program: &Program,
    virtual_remap: &BTreeMap<u16, (u8, u8)>,
    evaluate_recipe: &impl Fn(&MergedRecipe) -> E4,
) -> Result<SpecialGeometry, BwdVmLowerError> {
    let mut referenced = BTreeMap::<u16, BTreeSet<OperandField>>::new();
    visit_operands(program, |operand, field| {
        if let OperandLine::Special { desc } = *operand {
            if !virtual_remap.contains_key(&desc) {
                referenced.entry(desc).or_default().insert(field);
            }
        }
    });
    check_cap("specials", referenced.len(), BWD_VM_SPECIAL_CAP)?;

    // Validate the whole dense referenced namespace before evaluating any
    // recipe, so a structural error cannot leave observable partial work in a
    // stateful host evaluator.
    for &old in referenced.keys() {
        match compiled
            .compiled
            .specials
            .get(old)
            .ok_or(BwdVmLowerError::MissingSpecial { desc: old })?
        {
            BwdSpecial::Coefficient { fragment }
                if distilled
                    .fragments
                    .fragments
                    .get(*fragment as usize)
                    .is_none() =>
            {
                return Err(BwdVmLowerError::InvalidCoefficientFragment {
                    desc: old,
                    fragment: *fragment,
                });
            }
            BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(_),
            } => return Err(BwdVmLowerError::ReadFoldSpecial { desc: old }),
            BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup { .. },
            } => return Err(BwdVmLowerError::UnmappedVirtualSource { desc: old }),
            BwdSpecial::Coefficient { .. }
            | BwdSpecial::AccInit
            | BwdSpecial::VirtualSetup { .. } => {}
        }
    }

    // Coefficients retain original descriptor order. AccInit is deliberately
    // appended after every fragment coefficient even though the compiler
    // interns its descriptor first (fragment_descs); the upload ABI reserves
    // the terminal coefficient slot for the accumulator initializer.
    let mut coefficients = Vec::new();
    let mut coefficient_slots = BTreeMap::<u16, u32>::new();
    for &old in referenced.keys() {
        if let Some(BwdSpecial::Coefficient { fragment }) = compiled.compiled.specials.get(old) {
            check_cap(
                "coefficients",
                coefficients.len() + 1,
                BWD_VM_COEFFICIENT_CAP,
            )?;
            let recipe = &distilled.fragments.fragments[*fragment as usize].recipe;
            coefficient_slots.insert(old, coefficients.len() as u32);
            coefficients.push(evaluate_recipe(recipe));
        }
    }
    for &old in referenced.keys() {
        if matches!(
            compiled.compiled.specials.get(old),
            Some(BwdSpecial::AccInit)
        ) {
            check_cap(
                "coefficients",
                coefficients.len() + 1,
                BWD_VM_COEFFICIENT_CAP,
            )?;
            coefficient_slots.insert(old, coefficients.len() as u32);
            coefficients.push(evaluate_recipe(&distilled.fragments.c_init));
        }
    }

    let mut specials = Vec::with_capacity(referenced.len());
    let mut remap = BTreeMap::new();
    for (&old, fields) in &referenced {
        let special = compiled
            .compiled
            .specials
            .get(old)
            .ok_or(BwdVmLowerError::MissingSpecial { desc: old })?;
        let coefficient_slot = match special {
            BwdSpecial::Coefficient { .. } | BwdSpecial::AccInit => Some(coefficient_slots[&old]),
            BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(_),
            } => return Err(BwdVmLowerError::ReadFoldSpecial { desc: old }),
            BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup { .. },
            } => return Err(BwdVmLowerError::UnmappedVirtualSource { desc: old }),
            BwdSpecial::VirtualSetup { .. } => None,
        };
        let mut packed = None;
        for &field in fields {
            let candidate = BwdVmSpecial::from_special(special, field, coefficient_slot)
                .map_err(BwdVmLowerError::Special)?;
            if let Some(previous) = packed {
                debug_assert_eq!(previous, candidate);
            } else {
                packed = Some(candidate);
            }
        }
        let dense = specials.len() as u16;
        specials.push(packed.expect("a referenced special has at least one operand field"));
        remap.insert(old, dense);
    }
    Ok(SpecialGeometry {
        specials,
        coefficients,
        remap,
    })
}

fn rewrite_program(
    program: &Program,
    source_remap: &BTreeMap<(u8, u8), (u8, u8)>,
    virtual_remap: &BTreeMap<u16, (u8, u8)>,
    special_remap: &BTreeMap<u16, u16>,
) -> Result<Program, BwdVmLowerError> {
    let mut seen_virtual = BTreeSet::new();
    let mut remap_operand = |operand: OperandLine| -> Result<OperandLine, BwdVmLowerError> {
        Ok(match operand {
            OperandLine::Source {
                window,
                column,
                first_access,
            } => {
                let &(window, column) = source_remap
                    .get(&(window, column))
                    .ok_or(BwdVmLowerError::UnmappedSource { window, column })?;
                OperandLine::Source {
                    window,
                    column,
                    first_access,
                }
            }
            OperandLine::Special { desc } => {
                if let Some(&(window, column)) = virtual_remap.get(&desc) {
                    OperandLine::Source {
                        window,
                        column,
                        first_access: seen_virtual.insert(desc),
                    }
                } else {
                    OperandLine::Special {
                        desc: *special_remap
                            .get(&desc)
                            .ok_or(BwdVmLowerError::MissingSpecial { desc })?,
                    }
                }
            }
            other => other,
        })
    };

    let mut instrs = Vec::with_capacity(program.instrs.len());
    for instruction in &program.instrs {
        instrs.push(match instruction {
            Instr::Add {
                field,
                sign,
                promote,
                operands,
            } => Instr::Add {
                field: *field,
                sign: *sign,
                promote: *promote,
                operands: operands
                    .iter()
                    .copied()
                    .map(&mut remap_operand)
                    .collect::<Result<_, _>>()?,
            },
            Instr::Mul {
                field,
                promote,
                negate_acc,
                operands,
            } => Instr::Mul {
                field: *field,
                promote: *promote,
                negate_acc: *negate_acc,
                operands: operands
                    .iter()
                    .copied()
                    .map(&mut remap_operand)
                    .collect::<Result<_, _>>()?,
            },
            Instr::Fma {
                field_lhs,
                field_rhs,
                sign,
                promote,
                pairs,
            } => Instr::Fma {
                field_lhs: *field_lhs,
                field_rhs: *field_rhs,
                sign: *sign,
                promote: *promote,
                pairs: pairs
                    .iter()
                    .map(|&(lhs, rhs)| Ok((remap_operand(lhs)?, remap_operand(rhs)?)))
                    .collect::<Result<_, BwdVmLowerError>>()?,
            },
            Instr::Mov {
                dir,
                field,
                dst,
                src,
            } => Instr::Mov {
                dir: *dir,
                field: *field,
                dst: *dst,
                src: src.map(&mut remap_operand).transpose()?,
            },
        });
    }
    Ok(Program { instrs })
}

fn visit_operands(program: &Program, mut visit: impl FnMut(&OperandLine, OperandField)) {
    for instruction in &program.instrs {
        match instruction {
            Instr::Add {
                field, operands, ..
            }
            | Instr::Mul {
                field, operands, ..
            } => operands.iter().for_each(|operand| visit(operand, *field)),
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                for (lhs, rhs) in pairs {
                    visit(lhs, *field_lhs);
                    visit(rhs, *field_rhs);
                }
            }
            Instr::Mov {
                field,
                src: Some(src),
                ..
            } => visit(src, *field),
            Instr::Mov { src: None, .. } => {}
        }
    }
}

fn derived_e4_bank_len(compiled: &CompiledBackwardEvaluation, sub: LdcSub, cap: usize) -> usize {
    let mut len = 0usize;
    while len <= cap && compiled.compiled.derived_e4.get(sub, len as u16).is_some() {
        len += 1;
    }
    len
}

fn program_cell_count(program: &Program) -> usize {
    let mut max_cell = 0usize;
    let mut any = false;
    visit_operands(program, |operand, _| {
        if let OperandLine::Smem { cell } = *operand {
            any = true;
            max_cell = max_cell.max(cell as usize);
        }
    });
    for instruction in &program.instrs {
        if let Instr::Mov {
            dst: Some(DstLine::Smem { cell }),
            ..
        } = instruction
        {
            any = true;
            max_cell = max_cell.max(*cell as usize);
        }
    }
    usize::from(any) + max_cell
}

#[cfg(all(test, feature = "bench"))]
mod tests {
    use std::cell::Cell;
    use std::collections::{BTreeMap, BTreeSet};

    use cs::gkr_compiler::dag_ir::BwdRegime;
    use cs::gkr_compiler::dag_ir::{ChallengeKey, ChallengePower, ChallengeRef};
    use field::{Field, FieldExtension, PrimeField};
    use gkr_eval_isa::bwd::source::BwdSpecial;
    use gkr_eval_isa::fwd::encode::decode;
    use gkr_eval_isa::fwd::isa::{Instr, OperandField, OperandLine, Program};

    use super::*;
    use crate::primitives::field::{BF, E4};
    use crate::prover::gkr::backward::vm::compile::{load_add_sub_l0_case, AddSubBwdVmCase};
    use crate::prover::gkr::backward::vm::desc::{
        BWD_VM_SOURCE_WINDOW_CAP, BWD_VM_SPECIAL_KIND_ACC_INIT, BWD_VM_SPECIAL_KIND_COEFFICIENT,
        BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP,
    };
    use crate::prover::gkr::backward::GkrEqSizes;
    use crate::prover::gkr::forward::bench_interp::fixture::deterministic_backward_challenge_value;
    use crate::prover::gkr::forward::vm::lower::ResolvedColumn;
    use crate::upstream::GKRAddress;

    fn e4(value: u32) -> E4 {
        <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
    }

    fn visit_operands(program: &Program, mut visit: impl FnMut(&OperandLine, OperandField)) {
        for instruction in &program.instrs {
            match instruction {
                Instr::Add {
                    field, operands, ..
                }
                | Instr::Mul {
                    field, operands, ..
                } => operands.iter().for_each(|operand| visit(operand, *field)),
                Instr::Fma {
                    field_lhs,
                    field_rhs,
                    pairs,
                    ..
                } => {
                    for (lhs, rhs) in pairs {
                        visit(lhs, *field_lhs);
                        visit(rhs, *field_rhs);
                    }
                }
                Instr::Mov {
                    field,
                    src: Some(src),
                    ..
                } => visit(src, *field),
                Instr::Mov { src: None, .. } => {}
            }
        }
    }

    fn source_coordinates(program: &Program) -> Vec<(u8, u8)> {
        let mut coordinates = BTreeSet::new();
        visit_operands(program, |operand, _| {
            if let OperandLine::Source { window, column, .. } = *operand {
                coordinates.insert((window, column));
            }
        });
        coordinates.into_iter().collect()
    }

    fn fake_sources(
        case: &AddSubBwdVmCase,
        backing_depth: u8,
        target_depth: u8,
        materialize: bool,
    ) -> Vec<ResolvedBwdSourceWindow> {
        let fields = source_fields(&case.compiled.compiled.program)
            .expect("compiled source operands have one field");
        source_coordinates(&case.compiled.compiled.program)
            .into_iter()
            .map(|(window, column)| {
                let is_e4 = fields[&(window, column)] == OperandField::Ext;
                let stride = 0x1_000u32;
                let matrix_base = 0x1000_0000usize + window as usize * 0x0100_0000;
                let absolute = case.compiled.compiled.source_windows.windows()[window as usize]
                    .first_column
                    + column as usize;
                let read = ResolvedColumn {
                    is_e4,
                    ptr: (matrix_base + absolute * stride as usize) as *const u8,
                    matrix_base: matrix_base as *mut u8,
                    stride_bytes: stride,
                };
                let publish = materialize.then_some(ResolvedColumn {
                    is_e4,
                    ptr: (0x5000_0000usize
                        + window as usize * 0x0100_0000
                        + absolute * stride as usize) as *const u8,
                    matrix_base: (0x5000_0000usize + window as usize * 0x0100_0000) as *mut u8,
                    stride_bytes: stride,
                });
                ResolvedBwdSourceWindow {
                    logical_window: window,
                    logical_column: column,
                    read,
                    publish,
                    backing_depth,
                    target_depth,
                    materialize,
                }
            })
            .collect()
    }

    fn fake_virtual_sources(
        case: &AddSubBwdVmCase,
        backing_depth: u8,
        target_depth: u8,
        materialize: bool,
    ) -> Vec<ResolvedBwdVirtualSource> {
        let mut referenced = BTreeMap::new();
        visit_operands(&case.compiled.compiled.program, |operand, field| {
            let OperandLine::Special { desc } = *operand else {
                return;
            };
            let Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup { kind },
            }) = case.compiled.compiled.specials.get(desc)
            else {
                return;
            };
            assert_eq!(field, OperandField::Ext);
            referenced.insert(desc, virtual_setup_kind_code(kind) as usize);
        });

        referenced
            .into_iter()
            .map(|(desc, column)| {
                let stride_bytes = 0x1_000u32;
                let read_base = 0x6000_0000usize;
                let publish_base = 0x7000_0000usize;
                ResolvedBwdVirtualSource {
                    desc,
                    read: (backing_depth > 0).then_some(ResolvedColumn {
                        is_e4: true,
                        ptr: (read_base + column * stride_bytes as usize) as *const u8,
                        matrix_base: read_base as *mut u8,
                        stride_bytes,
                    }),
                    publish: materialize.then_some(ResolvedColumn {
                        is_e4: true,
                        ptr: (publish_base + column * stride_bytes as usize) as *const u8,
                        matrix_base: publish_base as *mut u8,
                        stride_bytes,
                    }),
                    backing_depth,
                    target_depth,
                    materialize,
                }
            })
            .collect()
    }

    fn runtime_with_virtual<'a>(
        round: u8,
        sources: &'a [ResolvedBwdSourceWindow],
        virtual_sources: &'a [ResolvedBwdVirtualSource],
        challenges: &'a [E4],
        resolve_source: &'a dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
    ) -> BwdVmRoundBinding<'a> {
        runtime(round, sources, virtual_sources, challenges, resolve_source)
    }

    fn runtime<'a>(
        round: u8,
        sources: &'a [ResolvedBwdSourceWindow],
        virtual_sources: &'a [ResolvedBwdVirtualSource],
        challenges: &'a [E4],
        resolve_source: &'a dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
    ) -> BwdVmRoundBinding<'a> {
        BwdVmRoundBinding {
            round,
            rows: 32,
            round_challenges: challenges,
            sources,
            virtual_sources,
            resolve_source,
            eq_low: 0x8800_0000usize as *const E4,
            eq_sizes: GkrEqSizes::zeroed(),
            contributions: 0x9900_0000usize as *mut E4,
        }
    }

    fn expected_sources(
        case: &AddSubBwdVmCase,
        sources: &[ResolvedBwdSourceWindow],
    ) -> BTreeMap<GKRAddress, ResolvedColumn> {
        sources
            .iter()
            .filter_map(|source| {
                case.compiled
                    .compiled
                    .source_windows
                    .resolve_read_place(source.logical_window, source.logical_column)
                    .map(|place| (read_place_to_gkr_address(&place), source.read))
            })
            .collect()
    }

    fn lower_case(
        case: &AddSubBwdVmCase,
        binding: &BwdVmRoundBinding<'_>,
    ) -> Result<BwdVmSetup, BwdVmLowerError> {
        lower_bwd_vm(
            &case.compiled,
            &case.distilled,
            binding,
            &|reference| e4(derived_tag(reference)),
            &|recipe| e4(recipe_tag(recipe)),
        )
    }

    fn lower_case_at(
        case: &AddSubBwdVmCase,
        round: u8,
        sources: &[ResolvedBwdSourceWindow],
        challenges: &[E4],
    ) -> Result<BwdVmSetup, BwdVmLowerError> {
        let expected = expected_sources(case, sources);
        let resolve_source = |address| expected.get(&address).copied();
        let virtual_sources = fake_virtual_sources(case, 0, round, false);
        lower_case(
            case,
            &runtime(
                round,
                sources,
                &virtual_sources,
                challenges,
                &resolve_source,
            ),
        )
    }

    fn derived_tag(reference: &crate::upstream::ChallengeRef) -> u32 {
        format!("{reference:?}")
            .bytes()
            .fold(0x811c_9dc5u32, |hash, byte| {
                (hash ^ byte as u32).wrapping_mul(0x0100_0193)
            })
    }

    fn recipe_tag(recipe: &gkr_eval_isa::bwd::fragment::MergedRecipe) -> u32 {
        recipe
            .terms
            .iter()
            .flat_map(|term| term.factors.iter())
            .fold(recipe.terms.len() as u32 + 1, |tag, factor| {
                tag.wrapping_mul(16777619).wrapping_add(factor.0)
            })
    }

    #[test]
    fn r0_plain_sources_bind_equal_depth_without_publish_and_keep_first_access() {
        let case = load_add_sub_l0_case(BwdRegime::R0, 2);
        let sources = fake_sources(&case, 0, 0, false);
        let setup = lower_case_at(&case, 0, &sources, &[]).unwrap();

        assert!(setup.desc.n_source_windows > 0);
        for window in &setup.desc.source_windows[..setup.desc.n_source_windows as usize] {
            assert_eq!(window.backing_depth, window.target_depth);
            assert!(window.publish_base.is_null());
            assert_eq!(window.materialize, 0);
        }

        let decoded = decode(&setup.desc.program[..setup.desc.program_lanes as usize]).unwrap();
        let mut expected = BTreeMap::<usize, Vec<bool>>::new();
        let bindings = sources
            .iter()
            .map(|binding| ((binding.logical_window, binding.logical_column), binding))
            .collect::<BTreeMap<_, _>>();
        visit_operands(&case.compiled.compiled.program, |operand, _| {
            if let OperandLine::Source {
                window,
                column,
                first_access,
            } = *operand
            {
                expected
                    .entry(bindings[&(window, column)].read.ptr as usize)
                    .or_default()
                    .push(first_access);
            }
        });
        let mut actual = BTreeMap::<usize, Vec<bool>>::new();
        visit_operands(&decoded, |operand, _| {
            if let OperandLine::Source {
                window,
                column,
                first_access,
            } = *operand
            {
                let physical = &setup.desc.source_windows[window as usize];
                actual
                    .entry(
                        physical.read_base as usize
                            + column as usize * physical.read_stride_bytes as usize,
                    )
                    .or_default()
                    .push(first_access);
            }
        });
        for accesses in expected.values_mut().chain(actual.values_mut()) {
            accesses.sort_unstable();
        }
        assert_eq!(actual, expected);
    }

    #[test]
    fn ext_lazy_round_two_binds_depth_zero_to_two() {
        let case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let sources = fake_sources(&case, 0, 2, false);
        let challenges = [e4(7), e4(11)];
        let setup = lower_case_at(&case, 2, &sources, &challenges).unwrap();

        for window in &setup.desc.source_windows[..setup.desc.n_source_windows as usize] {
            assert_eq!((window.backing_depth, window.target_depth), (0, 2));
            assert_eq!(window.materialize, 0);
        }
        assert_eq!(setup.desc.round_challenges, challenges.as_ptr());
        assert_eq!(setup.desc.n_round_challenges, 2);
    }

    #[test]
    fn ext_fold_sources_bind_the_operand_field_not_the_origin_field() {
        let case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let sources = fake_sources(&case, 0, 0, false);
        let fields = source_fields(&case.compiled.compiled.program)
            .expect("compiled source operands have one field");
        let (window, column) = fields
            .iter()
            .find_map(|(&coordinate, &field)| {
                (field == OperandField::Ext
                    && case
                        .compiled
                        .compiled
                        .source_windows
                        .source_field(coordinate.0)
                        == Some(OperandField::Base))
                .then_some(coordinate)
            })
            .expect("fixture has an Ext FoldSource over a base origin");
        assert!(
            sources
                .iter()
                .find(|source| {
                    (source.logical_window, source.logical_column) == (window, column)
                })
                .expect("source binding")
                .read
                .is_e4
        );
        lower_case_at(&case, 0, &sources, &[])
            .expect("lifted Ext backing must satisfy the operand field");
    }

    #[test]
    fn descriptor_exposes_only_the_active_round_challenge_prefix() {
        let case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let challenges = (0..24).map(|round| e4(0x80 + round)).collect::<Vec<_>>();
        let round_zero_sources = fake_sources(&case, 0, 0, false);
        let round_zero = lower_case_at(&case, 0, &round_zero_sources, &challenges)
            .expect("round-zero Ext descriptor");
        assert_eq!(
            round_zero.desc.n_round_challenges, 0,
            "Ext VirtualSetup must fold to the active round, not every supplied challenge"
        );

        let round_two_sources = fake_sources(&case, 0, 2, false);
        let round_two = lower_case_at(&case, 2, &round_two_sources, &challenges)
            .expect("round-two Ext descriptor");
        assert_eq!(round_two.desc.n_round_challenges, 2);
        assert!(matches!(
            lower_case_at(&case, 2, &round_two_sources, &challenges[..1]),
            Err(BwdVmLowerError::RoundChallengesTooShort {
                required: 2,
                actual: 1,
            })
        ));
    }

    #[test]
    fn bwd_vm_virtual_source_lowering() {
        let mut case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let virtual_desc = (0..case.compiled.compiled.specials.len() as u16)
            .find(|&desc| {
                matches!(
                    case.compiled.compiled.specials.get(desc),
                    Some(BwdSpecial::FoldSource {
                        origin: OriginLeaf::VirtualSetup { .. },
                    })
                )
            })
            .expect("Ext fixture has a virtual fold descriptor");
        let kind_code = match case.compiled.compiled.specials.get(virtual_desc) {
            Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup { kind },
            }) => virtual_setup_kind_code(kind) as u8,
            _ => unreachable!(),
        };
        let virtual_program = Program {
            instrs: vec![Instr::Add {
                field: OperandField::Ext,
                sign: gkr_eval_isa::fwd::isa::Sign::Plus,
                promote: false,
                operands: vec![
                    OperandLine::Special { desc: virtual_desc },
                    OperandLine::Special { desc: virtual_desc },
                ],
            }],
        };
        case.compiled.compiled.program = virtual_program.clone();
        case.compiled.encoded = encode(&virtual_program).unwrap();
        let no_sources = [];
        let resolve_none = |_| None;

        let round_two_virtuals = fake_virtual_sources(&case, 0, 2, false);
        let round_two_challenges = [e4(7), e4(11)];
        let setup = lower_case(
            &case,
            &runtime_with_virtual(
                2,
                &no_sources,
                &round_two_virtuals,
                &round_two_challenges,
                &resolve_none,
            ),
        )
        .unwrap();
        let decoded = decode(&setup.desc.program[..setup.desc.program_lanes as usize]).unwrap();
        let mut decoded_virtual_operands = Vec::new();
        visit_operands(&decoded, |operand, _| {
            decoded_virtual_operands.push(*operand);
        });
        let OperandLine::Source {
            window: virtual_window,
            ..
        } = decoded_virtual_operands[0]
        else {
            panic!("first virtual fold use must lower to a source");
        };
        assert_eq!(
            decoded_virtual_operands,
            [
                OperandLine::Source {
                    window: virtual_window,
                    column: kind_code,
                    first_access: true,
                },
                OperandLine::Source {
                    window: virtual_window,
                    column: kind_code,
                    first_access: false,
                },
            ]
        );
        let source = setup.desc.source_windows[virtual_window as usize];
        assert_eq!(source.materialize, 0);
        assert_eq!(source.backing_depth, 0);
        assert_eq!(source.target_depth, 2);

        let invalid_round_two_virtuals = fake_virtual_sources(&case, 0, 2, true);
        assert!(matches!(
            lower_case(
                &case,
                &runtime_with_virtual(
                    2,
                    &no_sources,
                    &invalid_round_two_virtuals,
                    &round_two_challenges,
                    &resolve_none,
                ),
            ),
            Err(BwdVmLowerError::InvalidVirtualMaterialization {
                target_depth: 2,
                materialize: true,
                ..
            })
        ));

        let impossible_round_two_continuation = fake_virtual_sources(&case, 1, 2, false);
        assert!(matches!(
            lower_case(
                &case,
                &runtime_with_virtual(
                    2,
                    &no_sources,
                    &impossible_round_two_continuation,
                    &round_two_challenges,
                    &resolve_none,
                ),
            ),
            Err(BwdVmLowerError::InvalidVirtualDepths {
                backing_depth: 1,
                target_depth: 2,
                ..
            })
        ));

        let round_three_virtuals = fake_virtual_sources(&case, 0, 3, true);
        let round_three_challenges = [e4(7), e4(11), e4(13)];
        let round_three = lower_case(
            &case,
            &runtime_with_virtual(
                3,
                &no_sources,
                &round_three_virtuals,
                &round_three_challenges,
                &resolve_none,
            ),
        )
        .unwrap();
        let source = round_three.desc.source_windows[virtual_window as usize];
        assert_eq!(source.materialize, 1);
        assert_eq!((source.backing_depth, source.target_depth), (0, 3));

        let invalid_round_three_virtuals = fake_virtual_sources(&case, 0, 3, false);
        assert!(matches!(
            lower_case(
                &case,
                &runtime_with_virtual(
                    3,
                    &no_sources,
                    &invalid_round_three_virtuals,
                    &round_three_challenges,
                    &resolve_none,
                ),
            ),
            Err(BwdVmLowerError::InvalidVirtualMaterialization {
                target_depth: 3,
                materialize: false,
                ..
            })
        ));

        let impossible_round_three_continuation = fake_virtual_sources(&case, 2, 3, true);
        assert!(matches!(
            lower_case(
                &case,
                &runtime_with_virtual(
                    3,
                    &no_sources,
                    &impossible_round_three_continuation,
                    &round_three_challenges,
                    &resolve_none,
                ),
            ),
            Err(BwdVmLowerError::InvalidVirtualDepths {
                backing_depth: 2,
                target_depth: 3,
                ..
            })
        ));

        let round_four_virtuals = fake_virtual_sources(&case, 3, 4, true);
        let round_four_challenges = [e4(7), e4(11), e4(13), e4(17)];
        let round_four = lower_case(
            &case,
            &runtime_with_virtual(
                4,
                &no_sources,
                &round_four_virtuals,
                &round_four_challenges,
                &resolve_none,
            ),
        )
        .unwrap();
        let source = round_four.desc.source_windows[virtual_window as usize];
        assert_eq!(source.materialize, 1);
        assert_eq!((source.backing_depth, source.target_depth), (3, 4));

        let mut r0 = load_add_sub_l0_case(BwdRegime::R0, 2);
        let plain_desc = (0..r0.compiled.compiled.specials.len() as u16)
            .find(|&desc| {
                matches!(
                    r0.compiled.compiled.specials.get(desc),
                    Some(BwdSpecial::VirtualSetup { .. })
                )
            })
            .expect("R0 fixture has a plain virtual descriptor");
        let r0_program = Program {
            instrs: vec![Instr::Add {
                field: OperandField::Base,
                sign: gkr_eval_isa::fwd::isa::Sign::Plus,
                promote: false,
                operands: vec![OperandLine::Special { desc: plain_desc }],
            }],
        };
        r0.compiled.compiled.program = r0_program.clone();
        r0.compiled.encoded = encode(&r0_program).unwrap();
        let r0_setup = lower_case(
            &r0,
            &runtime_with_virtual(0, &no_sources, &[], &[], &resolve_none),
        )
        .unwrap();
        let r0_decoded =
            decode(&r0_setup.desc.program[..r0_setup.desc.program_lanes as usize]).unwrap();
        assert!(matches!(
            r0_decoded.instrs[0],
            Instr::Add {
                ref operands,
                ..
            } if matches!(operands.as_slice(), [OperandLine::Special { .. }])
        ));
    }

    #[test]
    fn materialized_sources_bind_equal_depths_and_publish_geometry() {
        let case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let sources = fake_sources(&case, 2, 2, true);
        let challenges = [e4(7), e4(11)];
        let setup = lower_case_at(&case, 2, &sources, &challenges).unwrap();

        for window in &setup.desc.source_windows[..setup.desc.n_source_windows as usize] {
            if window.source_kind == BWD_VM_SOURCE_VIRTUAL {
                continue;
            }
            assert_eq!((window.backing_depth, window.target_depth), (2, 2));
            assert_eq!(window.materialize, 1);
            assert!(!window.publish_base.is_null());
            assert_ne!(window.read_base, window.publish_base.cast_const());
        }
        let decoded = decode(&setup.desc.program[..setup.desc.program_lanes as usize]).unwrap();
        let mut uses = BTreeMap::<(u8, u8), Vec<bool>>::new();
        visit_operands(&decoded, |operand, _| {
            if let OperandLine::Source {
                window,
                column,
                first_access,
            } = *operand
            {
                uses.entry((window, column)).or_default().push(first_access);
            }
        });
        assert!(uses
            .values()
            .any(|accesses| { accesses.contains(&true) && accesses.iter().any(|first| !first) }));
    }

    #[test]
    fn referenced_specials_are_dense_and_map_to_host_evaluated_slots() {
        let case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let sources = fake_sources(&case, 0, 2, false);
        let challenges = [e4(7), e4(11)];
        let virtual_sources = fake_virtual_sources(&case, 0, 2, false);
        let next_value = Cell::new(0u32);
        let expected = expected_sources(&case, &sources);
        let resolve_source = |address| expected.get(&address).copied();
        let setup = lower_bwd_vm(
            &case.compiled,
            &case.distilled,
            &runtime(2, &sources, &virtual_sources, &challenges, &resolve_source),
            &|reference| e4(derived_tag(reference)),
            &|_| {
                let slot = next_value.get();
                next_value.set(slot + 1);
                e4(0x1000 + slot)
            },
        )
        .unwrap();

        let mut old_fields = BTreeMap::<u16, BTreeSet<OperandField>>::new();
        visit_operands(&case.compiled.compiled.program, |operand, field| {
            if let OperandLine::Special { desc } = *operand {
                if !matches!(
                    case.compiled.compiled.specials.get(desc),
                    Some(BwdSpecial::FoldSource {
                        origin: OriginLeaf::VirtualSetup { .. },
                    })
                ) {
                    old_fields.entry(desc).or_default().insert(field);
                }
            }
        });
        assert_eq!(setup.desc.n_specials as usize, old_fields.len());

        let mut expected_slots = BTreeMap::new();
        let mut coefficient_slot = 0u32;
        for &old in old_fields.keys() {
            if matches!(
                case.compiled.compiled.specials.get(old),
                Some(BwdSpecial::Coefficient { .. })
            ) {
                expected_slots.insert(old, coefficient_slot);
                coefficient_slot += 1;
            }
        }
        for &old in old_fields.keys() {
            if matches!(
                case.compiled.compiled.specials.get(old),
                Some(BwdSpecial::AccInit)
            ) {
                expected_slots.insert(old, coefficient_slot);
                coefficient_slot += 1;
            }
        }
        let mut acc_init_slot = None;
        for (dense, old) in old_fields.keys().copied().enumerate() {
            let lowered = setup.desc.specials[dense];
            match case.compiled.compiled.specials.get(old).unwrap() {
                BwdSpecial::Coefficient { .. } => {
                    let slot = expected_slots[&old];
                    assert_eq!(lowered.kind(), BWD_VM_SPECIAL_KIND_COEFFICIENT);
                    assert_eq!(lowered.payload(), slot);
                    assert_eq!(setup.coefficients[slot as usize], e4(0x1000 + slot));
                }
                BwdSpecial::AccInit => {
                    let slot = expected_slots[&old];
                    assert_eq!(lowered.kind(), BWD_VM_SPECIAL_KIND_ACC_INIT);
                    assert_eq!(lowered.payload(), slot);
                    assert_eq!(setup.coefficients[slot as usize], e4(0x1000 + slot));
                    acc_init_slot = Some(slot);
                }
                BwdSpecial::VirtualSetup { .. }
                | BwdSpecial::FoldSource {
                    origin: gkr_eval_isa::bwd::source::OriginLeaf::VirtualSetup { .. },
                } => assert_eq!(lowered.kind(), BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP),
                BwdSpecial::FoldSource {
                    origin: gkr_eval_isa::bwd::source::OriginLeaf::Read(_),
                } => panic!("read-origin FoldSource survived final binding"),
            }
        }
        assert_eq!(setup.coefficients.len(), expected_slots.len());
        assert_eq!(next_value.get(), expected_slots.len() as u32);
        if let Some(acc_init_slot) = acc_init_slot {
            assert_eq!(acc_init_slot as usize + 1, setup.coefficients.len());
        }

        let decoded = decode(&setup.desc.program[..setup.desc.program_lanes as usize]).unwrap();
        visit_operands(&decoded, |operand, _| {
            if let OperandLine::Special { desc } = *operand {
                assert!((desc as u32) < setup.desc.n_specials);
            }
        });
    }

    #[test]
    fn keyed_source_bindings_are_order_independent() {
        let case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let sources = fake_sources(&case, 0, 2, false);
        let mut permuted = sources.clone();
        permuted.reverse();
        let challenges = [e4(7), e4(11)];

        let ordered = lower_case_at(&case, 2, &sources, &challenges).unwrap();
        let shuffled = lower_case_at(&case, 2, &permuted, &challenges).unwrap();

        assert_eq!(
            ordered.desc.program[..ordered.desc.program_lanes as usize],
            shuffled.desc.program[..shuffled.desc.program_lanes as usize]
        );
        assert_eq!(
            ordered.desc.n_source_windows,
            shuffled.desc.n_source_windows
        );
        assert_eq!(ordered.desc.n_specials, shuffled.desc.n_specials);
        assert_eq!(ordered.desc.n_coefficients, shuffled.desc.n_coefficients);
        for (ordered, shuffled) in ordered.desc.source_windows
            [..ordered.desc.n_source_windows as usize]
            .iter()
            .zip(&shuffled.desc.source_windows[..shuffled.desc.n_source_windows as usize])
        {
            assert_eq!(ordered.read_base, shuffled.read_base);
            assert_eq!(ordered.publish_base, shuffled.publish_base);
            assert_eq!(ordered.read_stride_bytes, shuffled.read_stride_bytes);
            assert_eq!(ordered.publish_stride_bytes, shuffled.publish_stride_bytes);
            assert_eq!(ordered.backing_depth, shuffled.backing_depth);
            assert_eq!(ordered.target_depth, shuffled.target_depth);
            assert_eq!(ordered.source_kind, shuffled.source_kind);
            assert_eq!(ordered.materialize, shuffled.materialize);
        }
        assert_eq!(ordered.coefficients, shuffled.coefficients);
        assert_eq!(ordered.const_derived_e4, shuffled.const_derived_e4);
    }

    #[test]
    fn lowering_rejects_swapped_same_field_sources_and_null_geometry() {
        let case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let challenges = [e4(7), e4(11)];
        let canonical = fake_sources(&case, 0, 2, false);
        let virtual_sources = fake_virtual_sources(&case, 0, 2, false);
        let expected = expected_sources(&case, &canonical);
        let resolve_source = |address| expected.get(&address).copied();

        let coordinates = source_coordinates(&case.compiled.compiled.program);
        let pair = coordinates
            .iter()
            .enumerate()
            .find_map(|(left, &(window, _))| {
                coordinates
                    .iter()
                    .enumerate()
                    .skip(left + 1)
                    .find(|(_, (other_window, _))| *other_window == window)
                    .map(|(right, _)| (left, right))
            })
            .expect("fixture has two same-field source columns");

        let mut swapped = canonical.clone();
        let left = swapped[pair.0].read;
        swapped[pair.0].read = swapped[pair.1].read;
        swapped[pair.1].read = left;
        assert!(matches!(
            lower_case(
                &case,
                &runtime(2, &swapped, &virtual_sources, &challenges, &resolve_source,)
            ),
            Err(BwdVmLowerError::SourceIdentityMismatch { .. })
        ));

        let mut null_read = canonical.clone();
        null_read[0].read.ptr = ptr::null();
        assert!(matches!(
            lower_case(
                &case,
                &runtime(
                    2,
                    &null_read,
                    &virtual_sources,
                    &challenges,
                    &resolve_source,
                )
            ),
            Err(BwdVmLowerError::NullSourceGeometry { .. })
        ));

        let mut null_publish = fake_sources(&case, 2, 2, true);
        null_publish[0].publish.as_mut().unwrap().ptr = ptr::null();
        assert!(matches!(
            lower_case_at(&case, 2, &null_publish, &challenges),
            Err(BwdVmLowerError::NullPublishGeometry { .. })
        ));
    }

    #[test]
    fn lowering_rejects_equal_depth_read_and_publish_aliases() {
        let case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let challenges = [e4(7), e4(11)];

        let mut read_alias = fake_sources(&case, 2, 2, true);
        read_alias[0].publish = Some(read_alias[1].read);
        assert!(matches!(
            lower_case_at(&case, 2, &read_alias, &challenges),
            Err(BwdVmLowerError::UnsafeReadPublishAlias { .. })
        ));

        let mut publish_alias = fake_sources(&case, 2, 2, true);
        publish_alias[1].publish = publish_alias[0].publish;
        assert!(matches!(
            lower_case_at(&case, 2, &publish_alias, &challenges),
            Err(BwdVmLowerError::UnsafePublishAlias { .. })
        ));
    }

    #[test]
    fn deterministic_backward_resolver_covers_transcript_only_challenges() {
        let claim = ChallengeRef {
            key: ChallengeKey::ClaimBatching,
            power: ChallengePower::One,
        };
        let claim_squared = ChallengeRef {
            key: ChallengeKey::ClaimBatching,
            power: ChallengePower::Static(2),
        };
        let constraint = ChallengeRef {
            key: ChallengeKey::ConstraintAggregation,
            power: ChallengePower::One,
        };
        let claim_value = deterministic_backward_challenge_value(&claim);
        let mut square = claim_value;
        square.mul_assign(&claim_value);
        assert_eq!(
            deterministic_backward_challenge_value(&claim_squared),
            square
        );
        assert_ne!(
            deterministic_backward_challenge_value(&constraint),
            claim_value
        );
    }

    #[test]
    fn all_thirty_add_sub_cases_lower_round_trip_and_omit_sparse_special_holes() {
        let mut cases = 0usize;
        let mut max_host_specials = 0usize;
        let mut max_dense_specials = 0usize;
        let mut max_omitted = 0usize;
        let mut saw_dense_special_census = false;
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            for budget in 2..=16 {
                let case = load_add_sub_l0_case(regime, budget);
                let round = u8::from(regime == BwdRegime::Ext) * 2;
                let sources = fake_sources(&case, 0, round, false);
                let challenges = [e4(7), e4(11)];
                let setup = lower_case_at(&case, round, &sources, &challenges[..round as usize])
                    .unwrap_or_else(|error| panic!("{regime:?} c{budget}: {error:?}"));
                let decoded =
                    decode(&setup.desc.program[..setup.desc.program_lanes as usize]).unwrap();
                let reencoded = gkr_eval_isa::fwd::encode::encode(&decoded).unwrap();
                assert_eq!(
                    reencoded,
                    setup.desc.program[..setup.desc.program_lanes as usize]
                );
                assert!(setup.desc.n_source_windows as usize <= BWD_VM_SOURCE_WINDOW_CAP);

                let mut referenced = BTreeSet::new();
                visit_operands(&case.compiled.compiled.program, |operand, _| {
                    if let OperandLine::Special { desc } = *operand {
                        if !matches!(
                            case.compiled.compiled.specials.get(desc),
                            Some(BwdSpecial::FoldSource {
                                origin: OriginLeaf::VirtualSetup { .. },
                            })
                        ) {
                            referenced.insert(desc);
                        }
                    }
                });
                let host = case.compiled.compiled.specials.len();
                max_host_specials = max_host_specials.max(host);
                max_dense_specials = max_dense_specials.max(referenced.len());
                max_omitted = max_omitted.max(host - referenced.len());
                saw_dense_special_census |=
                    host == 204 && referenced.len() == 145 && host - referenced.len() == 59;
                assert_eq!(setup.desc.n_specials as usize, referenced.len());
                cases += 1;
            }
        }
        assert_eq!(cases, 30);
        assert_eq!(max_host_specials, 204);
        assert_eq!(max_dense_specials, 147);
        assert_eq!(max_omitted, 59);
        assert!(saw_dense_special_census);
    }

    #[test]
    fn lowering_rejects_missing_field_stride_window_column_and_alias_bindings() {
        let case = load_add_sub_l0_case(BwdRegime::Ext, 2);
        let challenges = [e4(7), e4(11)];

        let mut missing = fake_sources(&case, 0, 2, false);
        missing.pop();
        assert!(matches!(
            lower_case_at(&case, 2, &missing, &challenges),
            Err(BwdVmLowerError::MissingSourceBinding { .. })
        ));

        let mut duplicate = fake_sources(&case, 0, 2, false);
        duplicate.push(duplicate[0]);
        assert!(matches!(
            lower_case_at(&case, 2, &duplicate, &challenges),
            Err(BwdVmLowerError::DuplicateSourceBinding { .. })
        ));

        let mut unknown = fake_sources(&case, 0, 2, false);
        unknown[0].logical_window = u8::MAX;
        assert!(matches!(
            lower_case_at(&case, 2, &unknown, &challenges),
            Err(BwdVmLowerError::UnknownSourceBinding { .. })
        ));

        let mut wrong_field = fake_sources(&case, 0, 2, false);
        wrong_field[0].read.is_e4 = !wrong_field[0].read.is_e4;
        assert!(matches!(
            lower_case_at(&case, 2, &wrong_field, &challenges),
            Err(BwdVmLowerError::SourceFieldMismatch { .. })
        ));

        let mut off_stride = fake_sources(&case, 0, 2, false);
        off_stride[0].read.ptr = (off_stride[0].read.matrix_base as usize + 1) as *const u8;
        assert!(matches!(
            lower_case_at(&case, 2, &off_stride, &challenges),
            Err(BwdVmLowerError::SourceColumnOffStride { .. })
        ));

        let mut wide = fake_sources(&case, 0, 2, false);
        let coordinates = source_coordinates(&case.compiled.compiled.program);
        let pair = coordinates
            .iter()
            .enumerate()
            .find_map(|(left, &(window, _))| {
                coordinates
                    .iter()
                    .enumerate()
                    .skip(left + 1)
                    .find(|(_, (other_window, _))| *other_window == window)
                    .map(|(right, _)| (left, right))
            })
            .expect("fixture has two coordinates in one source matrix");
        let base = wide[pair.0].read.matrix_base as usize;
        let stride = wide[pair.0].read.stride_bytes as usize;
        wide[pair.0].read.ptr = base as *const u8;
        wide[pair.1].read.ptr = (base + 128 * stride) as *const u8;
        assert!(matches!(
            lower_case_at(&case, 2, &wide, &challenges),
            Err(BwdVmLowerError::SourceColumnOverflow { .. })
        ));

        let mut too_many_windows = fake_sources(&case, 0, 2, false);
        assert!(too_many_windows.len() > BWD_VM_SOURCE_WINDOW_CAP);
        for (index, source) in too_many_windows.iter_mut().enumerate() {
            source.read.matrix_base = (0x7000_0000usize + index * 0x0010_0000) as *mut u8;
            source.read.ptr = source.read.matrix_base.cast_const();
        }
        assert!(matches!(
            lower_case_at(&case, 2, &too_many_windows, &challenges),
            Err(BwdVmLowerError::Capacity {
                field: "source_windows",
                cap: BWD_VM_SOURCE_WINDOW_CAP,
                ..
            })
        ));

        let mut alias = fake_sources(&case, 0, 2, true);
        for source in &mut alias {
            source.publish = Some(source.read);
        }
        assert!(matches!(
            lower_case_at(&case, 2, &alias, &challenges),
            Err(BwdVmLowerError::UnsafeReadPublishAlias { .. })
        ));

        let mut cross_alias = fake_sources(&case, 0, 2, true);
        cross_alias[0].publish = Some(cross_alias[1].read);
        assert!(matches!(
            lower_case_at(&case, 2, &cross_alias, &challenges),
            Err(BwdVmLowerError::UnsafeReadPublishAlias { .. })
        ));
    }
}
