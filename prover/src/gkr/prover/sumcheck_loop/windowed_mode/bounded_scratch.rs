//! Bounded-scratch ("DAG") variant of the initial windowed round: instead of one
//! `[F; 27]` / `[E; 27]` scratch entry per source polynomial (the full-size-scratch
//! strategy), the evaluation runs as an FSM over a fixed number of scratch slots.
//! A polynomial that is an input of multiple terms keeps its extrapolated form
//! resident in a slot until the scheduler evicts it; if a later term needs it
//! again it is re-read (and re-interpolated) from memory. The schedule is computed
//! once up front with Belady's (farthest-next-use) eviction policy, which is
//! optimal for a fixed term order.

use std::collections::BTreeSet;

use crate::gkr::PAR_THRESHOLD;

use super::*;
use crate::gkr::prover::sumcheck_loop::batch_evaluation::BatchedGKRDescription;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoundedStep {
    LoadBase {
        slot: u8,
        src_idx: u32,
        interpolate: bool,
    },
    LoadExt {
        slot: u8,
        src_idx: u32,
        interpolate: bool,
    },
    QuadraticBaseByBase {
        slot_a: u8,
        slot_b: u8,
        coeff_idx: u32,
    },
    QuadraticBaseByExt {
        slot_base: u8,
        slot_ext: u8,
        coeff_idx: u32,
    },
    QuadraticExtByExt {
        slot_a: u8,
        slot_b: u8,
        coeff_idx: u32,
    },
    LinearWithBase {
        slot: u8,
        coeff_idx: u32,
    },
    LinearWithExt {
        slot: u8,
        coeff_idx: u32,
    },
}

#[derive(Clone, Debug)]
pub struct BoundedScratchDescription<F: PrimeField, E: FieldExtension<F> + Field> {
    pub steps: Vec<BoundedStep>,
    pub constants: Vec<E>,
    pub total_additive_constant: E,
    pub num_base_slots: usize,
    pub num_ext_slots: usize,
    // stats to report scheduling quality
    pub num_distinct_base: usize,
    pub num_distinct_ext: usize,
    pub num_base_loads: usize,
    pub num_ext_loads: usize,
    pub _marker: core::marker::PhantomData<F>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Operand {
    Base(u32),
    Ext(u32),
}

// One abstract operation of the evaluation, before slot assignment.
#[derive(Clone, Copy, Debug)]
enum AbstractOp {
    QuadBB(u32, u32, u32),
    QuadBE(u32, u32, u32),
    QuadEE(u32, u32, u32),
    LinBase(u32, u32),
    LinExt(u32, u32),
}

impl AbstractOp {
    fn operands(&self) -> ([Option<Operand>; 2], u32) {
        match *self {
            AbstractOp::QuadBB(a, b, c) => ([Some(Operand::Base(a)), Some(Operand::Base(b))], c),
            AbstractOp::QuadBE(a, b, c) => ([Some(Operand::Base(a)), Some(Operand::Ext(b))], c),
            AbstractOp::QuadEE(a, b, c) => ([Some(Operand::Ext(a)), Some(Operand::Ext(b))], c),
            AbstractOp::LinBase(a, c) => ([Some(Operand::Base(a)), None], c),
            AbstractOp::LinExt(a, c) => ([Some(Operand::Ext(a)), None], c),
        }
    }
}

/// Build a bounded-scratch schedule for the same term order as
/// [`produce_descriptions_from_batched_description`] uses: quadratic chains first
/// (grouped by their `a` operand), linear terms merged in on the first sighting of
/// the poly, leftover linear terms at the end. Slot assignment uses Belady
/// eviction over the fixed order.
///
/// Returns the schedule plus the base/ext source address lists (in the same order
/// the `src_idx` fields refer to).
pub fn produce_bounded_scratch_description<F: PrimeField, E: FieldExtension<F> + Field>(
    description: &BatchedGKRDescription<F, E>,
    num_base_slots: usize,
    num_ext_slots: usize,
) -> (
    BoundedScratchDescription<F, E>,
    Vec<GKRAddress>,
    Vec<GKRAddress>,
) {
    let mut all_base_sources = BTreeSet::new();
    let mut all_ext_sources = BTreeSet::new();
    let mut base_sources_in_quadratic_evals = BTreeSet::new();
    let mut ext_sources_in_quadratic_evals = BTreeSet::new();

    for (a, other) in description.quadratic_part_base_by_base.iter() {
        all_base_sources.insert(*a);
        base_sources_in_quadratic_evals.insert(*a);
        for (b, _) in other.iter() {
            all_base_sources.insert(*b);
            base_sources_in_quadratic_evals.insert(*b);
        }
    }
    for (a, other) in description.quadratic_part_base_by_ext.iter() {
        all_base_sources.insert(*a);
        base_sources_in_quadratic_evals.insert(*a);
        for (b, _) in other.iter() {
            all_ext_sources.insert(*b);
            ext_sources_in_quadratic_evals.insert(*b);
        }
    }
    for (a, other) in description.quadratic_part_ext_by_ext.iter() {
        all_ext_sources.insert(*a);
        ext_sources_in_quadratic_evals.insert(*a);
        for (b, _) in other.iter() {
            all_ext_sources.insert(*b);
            ext_sources_in_quadratic_evals.insert(*b);
        }
    }
    for (a, _) in description.linear_part_base_by_everything.iter() {
        all_base_sources.insert(*a);
    }
    for (a, _) in description.linear_part_ext_by_everything.iter() {
        all_ext_sources.insert(*a);
    }

    let base_sources: Vec<_> = all_base_sources.iter().copied().collect();
    let ext_sources: Vec<_> = all_ext_sources.iter().copied().collect();

    let base_index =
        |addr: &GKRAddress| base_sources.iter().position(|el| el == addr).unwrap() as u32;
    let ext_index =
        |addr: &GKRAddress| ext_sources.iter().position(|el| el == addr).unwrap() as u32;

    let mut constants: Vec<E> = vec![];
    let mut ops: Vec<AbstractOp> = vec![];

    let mut linear_issued_for_base = BTreeSet::new();
    let mut linear_issued_for_ext = BTreeSet::new();

    let mut push_linear_base = |addr: &GKRAddress,
                                constants: &mut Vec<E>,
                                ops: &mut Vec<AbstractOp>,
                                linear_issued_for_base: &mut BTreeSet<GKRAddress>| {
        if linear_issued_for_base.contains(addr) {
            return;
        }
        for (el, coeff) in description.linear_part_base_by_everything.iter() {
            if el != addr {
                continue;
            }
            let coeff_idx = constants.len() as u32;
            constants.push(*coeff);
            ops.push(AbstractOp::LinBase(base_index(addr), coeff_idx));
            linear_issued_for_base.insert(*addr);
        }
    };
    let mut push_linear_ext = |addr: &GKRAddress,
                               constants: &mut Vec<E>,
                               ops: &mut Vec<AbstractOp>,
                               linear_issued_for_ext: &mut BTreeSet<GKRAddress>| {
        if linear_issued_for_ext.contains(addr) {
            return;
        }
        for (el, coeff) in description.linear_part_ext_by_everything.iter() {
            if el != addr {
                continue;
            }
            let coeff_idx = constants.len() as u32;
            constants.push(*coeff);
            ops.push(AbstractOp::LinExt(ext_index(addr), coeff_idx));
            linear_issued_for_ext.insert(*addr);
        }
    };

    for (a, other) in description.quadratic_part_base_by_base.iter() {
        for (b, coeff) in other.iter() {
            let coeff_idx = constants.len() as u32;
            constants.push(*coeff);
            ops.push(AbstractOp::QuadBB(base_index(a), base_index(b), coeff_idx));
            push_linear_base(b, &mut constants, &mut ops, &mut linear_issued_for_base);
        }
        push_linear_base(a, &mut constants, &mut ops, &mut linear_issued_for_base);
    }
    for (a, other) in description.quadratic_part_base_by_ext.iter() {
        for (b, coeff) in other.iter() {
            let coeff_idx = constants.len() as u32;
            constants.push(*coeff);
            ops.push(AbstractOp::QuadBE(base_index(a), ext_index(b), coeff_idx));
            push_linear_ext(b, &mut constants, &mut ops, &mut linear_issued_for_ext);
        }
        push_linear_base(a, &mut constants, &mut ops, &mut linear_issued_for_base);
    }
    for (a, other) in description.quadratic_part_ext_by_ext.iter() {
        for (b, coeff) in other.iter() {
            let coeff_idx = constants.len() as u32;
            constants.push(*coeff);
            ops.push(AbstractOp::QuadEE(ext_index(a), ext_index(b), coeff_idx));
            push_linear_ext(b, &mut constants, &mut ops, &mut linear_issued_for_ext);
        }
        push_linear_ext(a, &mut constants, &mut ops, &mut linear_issued_for_ext);
    }
    for (a, coeff) in description.linear_part_base_by_everything.iter() {
        if linear_issued_for_base.contains(a) {
            continue;
        }
        let coeff_idx = constants.len() as u32;
        constants.push(*coeff);
        ops.push(AbstractOp::LinBase(base_index(a), coeff_idx));
    }
    for (a, coeff) in description.linear_part_ext_by_everything.iter() {
        if linear_issued_for_ext.contains(a) {
            continue;
        }
        let coeff_idx = constants.len() as u32;
        constants.push(*coeff);
        ops.push(AbstractOp::LinExt(ext_index(a), coeff_idx));
    }

    // Belady slot assignment over the fixed op order, separately for the base
    // and ext slot pools.
    assert!(num_base_slots >= 2, "need at least two base slots");
    assert!(num_ext_slots >= 2, "need at least two ext slots");
    assert!(num_base_slots < 256 && num_ext_slots < 256);

    // next-use positions per operand
    let mut op_operand_lists: Vec<[Option<Operand>; 2]> = Vec::with_capacity(ops.len());
    for op in ops.iter() {
        op_operand_lists.push(op.operands().0);
    }
    use std::collections::BTreeMap;
    let mut uses: BTreeMap<Operand, Vec<usize>> = BTreeMap::new();
    for (pos, operands) in op_operand_lists.iter().enumerate() {
        for operand in operands.iter().flatten() {
            uses.entry(*operand).or_default().push(pos);
        }
    }
    // per-operand cursor into its use list
    let mut use_cursor: BTreeMap<Operand, usize> = uses.keys().map(|k| (*k, 0usize)).collect();

    let next_use_after = |uses: &BTreeMap<Operand, Vec<usize>>,
                          cursor: &BTreeMap<Operand, usize>,
                          operand: &Operand|
     -> usize {
        let list = &uses[operand];
        let c = cursor[operand];
        if c < list.len() {
            list[c]
        } else {
            usize::MAX
        }
    };

    struct Pool {
        // slot -> resident operand index (u32) or none
        resident: Vec<Option<u32>>,
        // operand idx -> slot
        location: BTreeMap<u32, u8>,
        loads: usize,
    }
    impl Pool {
        fn new(capacity: usize) -> Self {
            Pool {
                resident: vec![None; capacity],
                location: BTreeMap::new(),
                loads: 0,
            }
        }
    }

    let mut base_pool = Pool::new(num_base_slots);
    let mut ext_pool = Pool::new(num_ext_slots);

    let base_interp: Vec<bool> = base_sources
        .iter()
        .map(|el| base_sources_in_quadratic_evals.contains(el))
        .collect();
    let ext_interp: Vec<bool> = ext_sources
        .iter()
        .map(|el| ext_sources_in_quadratic_evals.contains(el))
        .collect();

    let mut steps: Vec<BoundedStep> = vec![];

    for (pos, op) in ops.iter().enumerate() {
        let (operands, coeff_idx) = op.operands();
        // ensure both operands resident, do not evict the other operand of this op
        let mut assigned_slots: [u8; 2] = [0; 2];
        for (i, operand) in operands.iter().enumerate() {
            let Some(operand) = operand else { continue };
            let (pool, is_base) = match operand {
                Operand::Base(_) => (&mut base_pool, true),
                Operand::Ext(_) => (&mut ext_pool, false),
            };
            let idx = match operand {
                Operand::Base(v) | Operand::Ext(v) => *v,
            };
            if let Some(slot) = pool.location.get(&idx) {
                assigned_slots[i] = *slot;
                continue;
            }
            // need a slot: free one?
            let protected: Option<u32> = match (i, &operands[1 - i]) {
                (1, Some(other)) | (0, Some(other)) => {
                    // protect the sibling operand if it lives in the same pool
                    match (operand, other) {
                        (Operand::Base(_), Operand::Base(v)) => Some(*v),
                        (Operand::Ext(_), Operand::Ext(v)) => Some(*v),
                        _ => None,
                    }
                }
                _ => None,
            };
            let slot = if let Some(free) = pool.resident.iter().position(|el| el.is_none()) {
                free as u8
            } else {
                // Belady: evict resident operand with farthest next use
                let mut victim_slot = u8::MAX;
                let mut victim_dist = 0usize;
                for (slot, resident) in pool.resident.iter().enumerate() {
                    let resident = resident.expect("full pool");
                    if Some(resident) == protected {
                        continue;
                    }
                    let victim_operand = if is_base {
                        Operand::Base(resident)
                    } else {
                        Operand::Ext(resident)
                    };
                    let dist = next_use_after(&uses, &use_cursor, &victim_operand);
                    if dist >= victim_dist {
                        victim_dist = dist;
                        victim_slot = slot as u8;
                    }
                }
                assert!(victim_slot != u8::MAX, "no evictable slot");
                let evicted = pool.resident[victim_slot as usize].unwrap();
                pool.location.remove(&evicted);
                victim_slot
            };
            pool.resident[slot as usize] = Some(idx);
            pool.location.insert(idx, slot);
            pool.loads += 1;
            if is_base {
                steps.push(BoundedStep::LoadBase {
                    slot,
                    src_idx: idx,
                    interpolate: base_interp[idx as usize],
                });
            } else {
                steps.push(BoundedStep::LoadExt {
                    slot,
                    src_idx: idx,
                    interpolate: ext_interp[idx as usize],
                });
            }
            assigned_slots[i] = slot;
        }
        // advance use cursors past `pos`
        for operand in operands.iter().flatten() {
            let cursor = use_cursor.get_mut(operand).unwrap();
            let list = &uses[operand];
            while *cursor < list.len() && list[*cursor] <= pos {
                *cursor += 1;
            }
        }

        match *op {
            AbstractOp::QuadBB(..) => steps.push(BoundedStep::QuadraticBaseByBase {
                slot_a: assigned_slots[0],
                slot_b: assigned_slots[1],
                coeff_idx,
            }),
            AbstractOp::QuadBE(..) => steps.push(BoundedStep::QuadraticBaseByExt {
                slot_base: assigned_slots[0],
                slot_ext: assigned_slots[1],
                coeff_idx,
            }),
            AbstractOp::QuadEE(..) => steps.push(BoundedStep::QuadraticExtByExt {
                slot_a: assigned_slots[0],
                slot_b: assigned_slots[1],
                coeff_idx,
            }),
            AbstractOp::LinBase(..) => steps.push(BoundedStep::LinearWithBase {
                slot: assigned_slots[0],
                coeff_idx,
            }),
            AbstractOp::LinExt(..) => steps.push(BoundedStep::LinearWithExt {
                slot: assigned_slots[0],
                coeff_idx,
            }),
        }
    }

    let descr = BoundedScratchDescription {
        steps,
        constants,
        total_additive_constant: description.constant_term,
        num_base_slots,
        num_ext_slots,
        num_distinct_base: base_sources.len(),
        num_distinct_ext: ext_sources.len(),
        num_base_loads: base_pool.loads,
        num_ext_loads: ext_pool.loads,
        _marker: core::marker::PhantomData,
    };

    (descr, base_sources, ext_sources)
}

pub fn evaluate_initial_with_bounded_scratch<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    description: &BoundedScratchDescription<F, E>,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    row_range: core::ops::Range<usize>,
) -> [E; 27] {
    assert!(input_size_log2 >= 4);
    assert_eq!(precomputed_eq_suffix.len(), 1 << (input_size_log2 - 3));
    let mut accumulator = [E::ZERO; 27];

    let input_size = 1 << input_size_log2;

    let mut base_field_scratch =
        vec![[F::ZERO; 27]; description.num_base_slots].into_boxed_slice();
    let mut ext_field_scratch = vec![[E::ZERO; 27]; description.num_ext_slots].into_boxed_slice();
    let mut eval_scratch = [E::ZERO; 27];

    for row in row_range {
        let eq_prefactor = &precomputed_eq_suffix[row];
        eval_scratch.fill(E::ZERO);

        for step in description.steps.iter() {
            match *step {
                BoundedStep::LoadBase {
                    slot,
                    src_idx,
                    interpolate,
                } => {
                    let dst = &mut base_field_scratch[slot as usize];
                    let src = &base_field_inputs[src_idx as usize];
                    if interpolate {
                        read_and_interpolate_field(dst, src, input_size, row);
                    } else {
                        read_without_interpolation(dst, src, input_size, row);
                    }
                }
                BoundedStep::LoadExt {
                    slot,
                    src_idx,
                    interpolate,
                } => {
                    let dst = &mut ext_field_scratch[slot as usize];
                    let src = &ext_field_inputs[src_idx as usize];
                    if interpolate {
                        read_and_interpolate_field(dst, src, input_size, row);
                    } else {
                        read_without_interpolation(dst, src, input_size, row);
                    }
                }
                BoundedStep::QuadraticBaseByBase {
                    slot_a,
                    slot_b,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_quadratic_base(
                        &mut eval_scratch,
                        &base_field_scratch[slot_a as usize],
                        &base_field_scratch[slot_b as usize],
                        &coeff,
                    );
                }
                BoundedStep::QuadraticBaseByExt {
                    slot_base,
                    slot_ext,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_quadratic_mixed(
                        &mut eval_scratch,
                        &ext_field_scratch[slot_ext as usize],
                        &base_field_scratch[slot_base as usize],
                        &coeff,
                    );
                }
                BoundedStep::QuadraticExtByExt {
                    slot_a,
                    slot_b,
                    coeff_idx,
                } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_quadratic_ext(
                        &mut eval_scratch,
                        &ext_field_scratch[slot_a as usize],
                        &ext_field_scratch[slot_b as usize],
                        &coeff,
                    );
                }
                BoundedStep::LinearWithBase { slot, coeff_idx } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_linear_base(
                        &mut eval_scratch,
                        &base_field_scratch[slot as usize],
                        &coeff,
                    );
                }
                BoundedStep::LinearWithExt { slot, coeff_idx } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_linear_ext(
                        &mut eval_scratch,
                        &ext_field_scratch[slot as usize],
                        &coeff,
                    );
                }
            }
        }

        if description.total_additive_constant.is_zero() == false {
            // only terms that are not at infinity
            for i in 0..2 {
                let offset = 9 * i;
                for j in 0..2 {
                    let offset = offset + 3 * j;
                    for k in 0..2 {
                        eval_scratch[offset + k].add_assign(&description.total_additive_constant);
                    }
                }
            }
        }

        accumulate_scaled(&mut accumulator, &eval_scratch, eq_prefactor);
    }

    accumulator
}

pub fn evaluate_initial_with_bounded_scratch_parallel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    base_field_inputs: Vec<DisjointAccessQuasiSlice<F, false>>,
    ext_field_inputs: Vec<DisjointAccessQuasiSlice<E, false>>,
    description: &BoundedScratchDescription<F, E>,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    worker: &Worker,
) -> [E; 27] {
    assert!(input_size_log2 >= 3);
    let work_size = (1 << input_size_log2) / 8;

    let geometry = worker.get_geometry_with_threshold(work_size, PAR_THRESHOLD);
    let mut acc_chunks = vec![[E::ZERO; 27]; geometry.num_chunks];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);

            let base_field_inputs = base_field_inputs.clone();
            let ext_field_inputs = ext_field_inputs.clone();
            let acc_dst = it.next().expect("dst chunk");

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                *acc_dst = evaluate_initial_with_bounded_scratch(
                    &base_field_inputs,
                    &ext_field_inputs,
                    description,
                    precomputed_eq_suffix,
                    input_size_log2,
                    chunk_start..(chunk_start + chunk_size),
                );
            })
        }
    });

    let mut acc = acc_chunks.pop().unwrap();
    for el in acc_chunks.into_iter() {
        for i in 0..27 {
            acc[i].add_assign(&el[i]);
        }
    }

    acc
}
