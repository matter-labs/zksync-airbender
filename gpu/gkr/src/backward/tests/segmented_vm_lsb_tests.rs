//! Address oracle for the segmented main-layer backward VM.
//!
//! The reference is an INDEPENDENT host transcription of the LSB-dense address
//! algebra the segmented VM is being converted to:
//!
//! * a target endpoint carries the logical index `u = 2 * row + b`, the endpoint
//!   bit `b` lowest;
//! * a source whose backing sits `delta` levels below the target depth reads its
//!   leaves at `raw[(u << delta) + q]`, `q = 0 .. 2^delta - 1`;
//! * leaf `q` carries the Lagrange weight `prod_j w_j` over the `delta`
//!   coordinates, with `w_j = c_j` when `(q >> j) & 1` is set and `1 - c_j`
//!   otherwise, and `c_j = claim_point[round - delta + j]`;
//! * a publication writes the two endpoints to `cache[2 * row]` and
//!   `cache[2 * row + 1]`.
//!
//! Every published fold is compared element by element in physical order over
//! the WHOLE destination backing before any launch reads it back, so a
//! split-half publication paired with a split-half reread cannot cancel.

use std::collections::BTreeSet;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use gpu_gkr_compiler::{
    ImmediateId, LEAN_CLASS_SHIFT, LEAN_CONT_GROUP_HEADER_CLASS, LEAN_CONT_OPCODES,
    LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2, LEAN_R0_OPCODES, SOURCE_NONE,
};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::backward::kernels::{
    get_eq_high_constant_device_ptr, get_main_layer_claim_point_device_ptr, GkrEqSizes,
    GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS, MAX_MAIN_LAYER_CLAIM_POINT_LEN,
};
use crate::backward::vm::seg::{
    bwd_seg_coeff_bank_device_ptr, launch_bwd_seg_continuation, launch_bwd_seg_r0,
};
use crate::backward::vm::seg_desc::{
    bwd_seg_lane, BwdSegAddrSlot, BwdSegDesc, BwdSegSourceRecord, BWD_COEFF_ORIGIN_PROCEDURAL,
    BWD_COEFF_ORIGIN_READ_BASE, BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_NONE,
    BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS, BWD_SEG_ADDR_COLUMN_BITS, BWD_SEG_ADDR_NONE,
    BWD_SEG_C_INIT_NONE, BWD_SEG_MAX_K, BWD_SEG_OUTPUT_BANK,
};
use crate::backward::vm::seg_lower::zeroed_box;
use crate::test_utils::make_test_context;
use crate::upstream::{Field, PrimeField};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::WARP_SIZE;
use gpu_prover_context::ProverContext;

/// Source classes, mirroring `seg_lower::SourceClass` (which is private to the
/// `vm` module) and the `BWD_SEG_SOURCE_CLASS_*` bytes it travels in.
const CLASS_BF_DIRECT: u8 = 0;
const CLASS_BF_INLINE_D1: u8 = 1;
const CLASS_BF_INLINE_D2: u8 = 2;
const CLASS_E4_DIRECT: u8 = 3;
const CLASS_PROCEDURAL_INLINE: u8 = 4;

/// Deepest fold the prologue materializes.
const MAX_DELTA: usize = 3;
/// Coefficient-bank slots the fixtures draw from.
const LIVE_BANK: usize = 64;
/// Immediates the fixtures install.
const LIVE_IMMEDIATES: usize = 4;

const COLUMN_MASK: u16 = (1u16 << BWD_SEG_ADDR_COLUMN_BITS) - 1;

fn lane_slot(lane: u16) -> usize {
    usize::from(lane >> BWD_SEG_ADDR_COLUMN_BITS)
}

fn lane_column(lane: u16) -> usize {
    usize::from(lane & COLUMN_MASK)
}

fn poison() -> E4 {
    E4::from_array_of_base(std::array::from_fn(|i| {
        BF::from_u32_with_reduction(0x0bad_beef + i as u32)
    }))
}

fn lift(value: BF) -> E4 {
    E4::from_array_of_base([value, BF::ZERO, BF::ZERO, BF::ZERO])
}

fn random_e4(rng: &mut StdRng) -> E4 {
    E4::from_array_of_base(std::array::from_fn(|_| {
        BF::from_u32_with_reduction(rng.random())
    }))
}

fn add(a: E4, b: E4) -> E4 {
    let mut v = a;
    v.add_assign(&b);
    v
}

fn sub(a: E4, b: E4) -> E4 {
    let mut v = a;
    v.sub_assign(&b);
    v
}

fn mul(a: E4, b: E4) -> E4 {
    let mut v = a;
    v.mul_assign(&b);
    v
}

fn bf_sub(a: BF, b: BF) -> BF {
    let mut v = a;
    v.sub_assign(&b);
    v
}

fn bf_mul(a: BF, b: BF) -> BF {
    let mut v = a;
    v.mul_assign(&b);
    v
}

/// Host mirror of `gkr_virtual_base_value` for the range-check-16 kind.
fn virtual_bf(index: usize) -> BF {
    if index < (1 << 16) {
        BF::from_u32_unchecked(index as u32)
    } else {
        BF::ZERO
    }
}

fn r0_class(index: usize) -> u16 {
    LEAN_R0_OPCODES[index].0
}

fn ext_class(index: usize) -> u16 {
    LEAN_CONT_OPCODES[index].0
}

fn upload_bf(context: &ProverContext, host: &[BF]) -> DeviceAllocation<BF> {
    let mut device: DeviceAllocation<BF> = context
        .alloc(host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device, host, context.get_exec_stream()).unwrap();
    device
}

fn upload_e4(context: &ProverContext, host: &[E4]) -> DeviceAllocation<E4> {
    let mut device: DeviceAllocation<E4> = context
        .alloc(host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device, host, context.get_exec_stream()).unwrap();
    device
}

fn download_e4(context: &ProverContext, device: &DeviceAllocation<E4>) -> Vec<E4> {
    let mut host = vec![E4::ZERO; device.len()];
    memory_copy_async(&mut host, device, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn write_symbol(context: &ProverContext, ptr: *mut E4, host: &[E4]) {
    // SAFETY: every symbol written here is at least `host.len()` E4 long, as
    // pinned by MAX_MAIN_LAYER_CLAIM_POINT_LEN, BWD_SEG_OUTPUT_BANK and the
    // eq-high shape.
    let view = unsafe { DeviceSlice::from_raw_parts_mut(ptr, host.len()) };
    memory_copy_async(view, host, context.get_exec_stream()).unwrap();
}

/// One addressing slot's backing.
enum Store {
    Bf(Vec<BF>, DeviceAllocation<BF>),
    Ext(Vec<E4>, DeviceAllocation<E4>),
    Procedural,
}

struct Slot {
    store: Store,
    log2_stride: u32,
}

impl Slot {
    fn origin(&self) -> u8 {
        match self.store {
            Store::Bf(..) => BWD_COEFF_ORIGIN_READ_BASE,
            Store::Ext(..) => BWD_COEFF_ORIGIN_READ_EXT,
            Store::Procedural => BWD_COEFF_ORIGIN_PROCEDURAL,
        }
    }

    fn procedural_kind(&self) -> u8 {
        match self.store {
            Store::Procedural => BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS,
            _ => BWD_COEFF_PROCEDURAL_NONE,
        }
    }

    fn base(&self) -> *const u8 {
        match &self.store {
            Store::Bf(_, device) => device.as_ptr() as *const u8,
            Store::Ext(_, device) => device.as_ptr() as *const u8,
            Store::Procedural => std::ptr::null(),
        }
    }
}

/// One source-table entry of a stage.
struct Src {
    src: u16,
    cache: Option<u16>,
    class: u8,
    delta: u8,
}

/// One program record: a plain term, or a coefficient group and its members
/// (`class`, immediate id, `source_a`, `source_b`).
enum Term {
    T {
        class: u16,
        coeff: u16,
        a: u16,
        b: u16,
    },
    G {
        core: u16,
        flags: u16,
        members: Vec<(u16, u16, u16, u16)>,
    },
}

fn unary(class: u16, coeff: u16, a: u16) -> Term {
    Term::T {
        class,
        coeff,
        a,
        b: SOURCE_NONE,
    }
}

fn binary(class: u16, coeff: u16, a: u16, b: u16) -> Term {
    Term::T { class, coeff, a, b }
}

/// One launch of the segmented VM.
struct Stage {
    name: &'static str,
    r0: bool,
    rows: usize,
    round: u32,
    sources: Vec<Src>,
    /// Source-table indices the prologue folds, in host order.
    fold_order: Vec<usize>,
    /// One term list per warp; `warps.len()` is `k`.
    warps: Vec<Vec<Term>>,
}

struct Fixture<'a> {
    context: &'a ProverContext,
    label: &'static str,
    slots: Vec<Slot>,
    coeff: Vec<E4>,
    immediates: Vec<BF>,
    claim: Vec<E4>,
    rng: StdRng,
    /// Every base-field cell the fixture has handed out. A backing entry must be
    /// distinct from every other one — a repeated or index-affine fill lets an
    /// address permutation cancel, and an equal-gap difference collapses the
    /// delta projection outright.
    seen: BTreeSet<u32>,
}

impl<'a> Fixture<'a> {
    /// Installs a fresh claim point, coefficient bank and identity eq-high
    /// slabs. The claim point is poisoned past its live prefix so an off-by-one
    /// on the round-to-coordinate map shows up as a mismatch.
    fn new(context: &'a ProverContext, label: &'static str, seed: u64, claim_len: usize) -> Self {
        let mut rng = StdRng::seed_from_u64(seed);
        assert!(claim_len <= MAX_MAIN_LAYER_CLAIM_POINT_LEN);
        let claim: Vec<E4> = (0..claim_len).map(|_| random_e4(&mut rng)).collect();
        let mut claim_symbol = vec![poison(); MAX_MAIN_LAYER_CLAIM_POINT_LEN];
        claim_symbol[..claim_len].copy_from_slice(&claim);
        write_symbol(
            context,
            get_main_layer_claim_point_device_ptr(),
            &claim_symbol,
        );

        let mut coeff = vec![E4::ZERO; BWD_SEG_OUTPUT_BANK];
        for slot in coeff[..LIVE_BANK].iter_mut() {
            *slot = random_e4(&mut rng);
        }
        write_symbol(context, bwd_seg_coeff_bank_device_ptr(), &coeff);

        write_symbol(
            context,
            get_eq_high_constant_device_ptr(),
            &vec![E4::ONE; GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN],
        );

        let immediates: Vec<BF> = (0..LIVE_IMMEDIATES)
            .map(|_| BF::from_u32_with_reduction(rng.random()))
            .collect();

        Self {
            context,
            label,
            slots: Vec::new(),
            coeff,
            immediates,
            claim,
            rng,
            seen: BTreeSet::new(),
        }
    }

    /// A base-field cell no other cell of this fixture holds.
    fn fresh_bf(&mut self) -> BF {
        loop {
            let value = BF::from_u32_with_reduction(self.rng.random());
            if self.seen.insert(value.as_u32_raw_repr_reduced()) {
                return value;
            }
        }
    }

    fn fresh_e4(&mut self) -> E4 {
        let coefficients: [BF; 4] = std::array::from_fn(|_| self.fresh_bf());
        E4::from_array_of_base(coefficients)
    }

    fn add_bf(&mut self, columns: usize, log2_stride: u32) -> usize {
        let host: Vec<BF> = (0..columns << log2_stride)
            .map(|_| self.fresh_bf())
            .collect();
        let device = upload_bf(self.context, &host);
        self.slots.push(Slot {
            store: Store::Bf(host, device),
            log2_stride,
        });
        self.slots.len() - 1
    }

    fn add_e4(&mut self, columns: usize, log2_stride: u32) -> usize {
        let host: Vec<E4> = (0..columns << log2_stride)
            .map(|_| self.fresh_e4())
            .collect();
        let device = upload_e4(self.context, &host);
        self.slots.push(Slot {
            store: Store::Ext(host, device),
            log2_stride,
        });
        self.slots.len() - 1
    }

    /// A publication destination: poison everywhere, so the comparison against
    /// the whole backing doubles as a written-everywhere and an overrun check.
    fn add_dest(&mut self, columns: usize, log2_stride: u32) -> usize {
        let host = vec![poison(); columns << log2_stride];
        let device = upload_e4(self.context, &host);
        self.slots.push(Slot {
            store: Store::Ext(host, device),
            log2_stride,
        });
        self.slots.len() - 1
    }

    /// A single-column E4 backing holding a basis vector. Basis probes are the
    /// one place the distinctness rule does not apply: each probe isolates one
    /// cell and the sweep over every cell determines the whole linear map, so
    /// no address permutation can cancel.
    fn add_e4_basis(&mut self, log2_stride: u32, hot: usize) -> usize {
        let host: Vec<E4> = (0..1usize << log2_stride)
            .map(|i| if i == hot { E4::ONE } else { E4::ZERO })
            .collect();
        let device = upload_e4(self.context, &host);
        self.slots.push(Slot {
            store: Store::Ext(host, device),
            log2_stride,
        });
        self.slots.len() - 1
    }

    fn add_procedural(&mut self) -> usize {
        self.slots.push(Slot {
            store: Store::Procedural,
            log2_stride: 0,
        });
        self.slots.len() - 1
    }

    fn lane(&self, slot: usize, column: usize) -> u16 {
        bwd_seg_lane(slot, column).unwrap()
    }

    // ── The oracle ──────────────────────────────────────────────────────────

    /// The `2^delta` Lagrange weights of a depth-`delta` fold at `round`, weight
    /// `q` taking coordinate `round - delta + j` on bit `j` of `q`.
    fn weights(&self, delta: usize, round: u32) -> Vec<E4> {
        if delta as u32 > round {
            return vec![E4::ZERO; 1 << delta];
        }
        (0..1usize << delta)
            .map(|q| {
                let mut w = E4::ONE;
                for j in 0..delta {
                    let c = self.claim[round as usize - delta + j];
                    w = mul(
                        w,
                        if (q >> j) & 1 == 1 {
                            c
                        } else {
                            sub(E4::ONE, c)
                        },
                    );
                }
                w
            })
            .collect()
    }

    fn leaf_bf(&self, lane: u16, index: usize) -> BF {
        let slot = &self.slots[lane_slot(lane)];
        match &slot.store {
            Store::Bf(host, _) => host[(lane_column(lane) << slot.log2_stride) + index],
            Store::Procedural => virtual_bf(index),
            Store::Ext(..) => panic!("{}: base-field read of an E4 backing", self.label),
        }
    }

    fn leaf_e4(&self, lane: u16, index: usize) -> E4 {
        let slot = &self.slots[lane_slot(lane)];
        match &slot.store {
            Store::Ext(host, _) => host[(lane_column(lane) << slot.log2_stride) + index],
            _ => lift(self.leaf_bf(lane, index)),
        }
    }

    /// The target-depth value at logical endpoint index `u`.
    fn folded(&self, lane: u16, delta: u8, u: usize, weights: &[E4]) -> E4 {
        let mut acc = E4::ZERO;
        for (q, weight) in weights.iter().enumerate() {
            acc = add(acc, mul(*weight, self.leaf_e4(lane, (u << delta) + q)));
        }
        acc
    }

    /// `(endpoint0, delta)` of one E4 source at `row`.
    fn source_e4(&self, stage: &Stage, index: u16, row: usize, weights: &[Vec<E4>]) -> (E4, E4) {
        let source = &stage.sources[usize::from(index)];
        // An `E4Direct` source that published this round is read back from the
        // destination it published into, at target depth.
        let (lane, delta) = if source.class == CLASS_E4_DIRECT {
            (source.cache.unwrap_or(source.src), 0)
        } else {
            (source.src, source.delta)
        };
        let w = &weights[usize::from(delta)];
        let e0 = self.folded(lane, delta, 2 * row, w);
        let e1 = self.folded(lane, delta, 2 * row + 1, w);
        (e0, sub(e1, e0))
    }

    /// `(endpoint0, delta)` of one base-field source at `row`. Base-field
    /// operands occur only at R0 and are never folded.
    fn source_bf(&self, stage: &Stage, index: u16, row: usize) -> (BF, BF) {
        let source = &stage.sources[usize::from(index)];
        assert!(
            source.class == CLASS_BF_DIRECT || source.class == CLASS_PROCEDURAL_INLINE,
            "{}: base-field operand of a class the bf resolver does not serve",
            self.label
        );
        let e0 = self.leaf_bf(source.src, 2 * row);
        let e1 = self.leaf_bf(source.src, 2 * row + 1);
        (e0, bf_sub(e1, e0))
    }

    fn apply_immediate(&self, immediate: u16, value: E4, sum: &mut E4) {
        if immediate == ImmediateId::ONE.0 {
            *sum = add(*sum, value);
        } else if immediate == ImmediateId::NEG_ONE.0 {
            *sum = sub(*sum, value);
        } else {
            let scalar = self.immediates[usize::from(immediate - ImmediateId::RESERVED)];
            *sum = add(*sum, mul(value, lift(scalar)));
        }
    }

    fn apply_term(
        &self,
        stage: &Stage,
        class: u16,
        coeff: u16,
        a: u16,
        b: u16,
        row: usize,
        weights: &[Vec<E4>],
        acc_c0: &mut E4,
        acc_c2: &mut E4,
    ) {
        let coefficient = self.coeff[usize::from(coeff)];
        if stage.r0 {
            if class == r0_class(0) {
                let (e0, _) = self.source_bf(stage, a, row);
                *acc_c0 = add(*acc_c0, mul(coefficient, lift(e0)));
            } else if class == r0_class(1) {
                let (e0, _) = self.source_e4(stage, a, row, weights);
                *acc_c0 = add(*acc_c0, mul(coefficient, e0));
            } else if class == r0_class(2) {
                let (_, da) = self.source_bf(stage, a, row);
                let (_, db) = self.source_bf(stage, b, row);
                *acc_c2 = add(*acc_c2, mul(coefficient, lift(bf_mul(da, db))));
            } else if class == r0_class(3) {
                let (_, da) = self.source_bf(stage, a, row);
                let (_, db) = self.source_e4(stage, b, row, weights);
                *acc_c2 = add(*acc_c2, mul(coefficient, mul(db, lift(da))));
            } else if class == r0_class(4) {
                let (_, da) = self.source_e4(stage, a, row, weights);
                let (_, db) = self.source_e4(stage, b, row, weights);
                *acc_c2 = add(*acc_c2, mul(coefficient, mul(da, db)));
            } else {
                panic!("{}: R0 term at a dead class {class}", self.label);
            }
            return;
        }
        if class == ext_class(0) {
            let (e0, _) = self.source_e4(stage, a, row, weights);
            *acc_c0 = add(*acc_c0, mul(coefficient, e0));
        } else if class == ext_class(1) {
            let (e0a, da) = self.source_e4(stage, a, row, weights);
            let (e0b, db) = self.source_e4(stage, b, row, weights);
            *acc_c0 = add(*acc_c0, mul(coefficient, mul(e0a, e0b)));
            *acc_c2 = add(*acc_c2, mul(coefficient, mul(da, db)));
        } else {
            panic!("{}: continuation term at a dead class {class}", self.label);
        }
    }

    /// The `(c0, c2)` this row contributes before eq.
    fn eval_row(&self, stage: &Stage, row: usize, weights: &[Vec<E4>]) -> (E4, E4) {
        let mut acc_c0 = E4::ZERO;
        let mut acc_c2 = E4::ZERO;
        for warp in &stage.warps {
            for term in warp {
                match term {
                    Term::T { class, coeff, a, b } => self.apply_term(
                        stage,
                        *class,
                        *coeff,
                        *a,
                        *b,
                        row,
                        weights,
                        &mut acc_c0,
                        &mut acc_c2,
                    ),
                    Term::G {
                        core,
                        flags,
                        members,
                    } => {
                        let mut sum_c0 = E4::ZERO;
                        let mut sum_c2 = E4::ZERO;
                        for (class, immediate, a, b) in members {
                            if *class == ext_class(0) {
                                let (e0, _) = self.source_e4(stage, *a, row, weights);
                                self.apply_immediate(*immediate, e0, &mut sum_c0);
                            } else if *class == ext_class(1) {
                                let (e0a, da) = self.source_e4(stage, *a, row, weights);
                                let (e0b, db) = self.source_e4(stage, *b, row, weights);
                                self.apply_immediate(*immediate, mul(e0a, e0b), &mut sum_c0);
                                self.apply_immediate(*immediate, mul(da, db), &mut sum_c2);
                            } else {
                                panic!("{}: group member at a dead class {class}", self.label);
                            }
                        }
                        let core = self.coeff[usize::from(*core)];
                        if *flags & LEAN_GROUP_FLAG_C0 != 0 {
                            acc_c0 = add(acc_c0, mul(core, sum_c0));
                        }
                        if *flags & LEAN_GROUP_FLAG_C2 != 0 {
                            acc_c2 = add(acc_c2, mul(core, sum_c2));
                        }
                    }
                }
            }
        }
        (acc_c0, acc_c2)
    }

    // ── One launch ──────────────────────────────────────────────────────────

    fn descriptor(
        &self,
        stage: &Stage,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
    ) -> Box<BwdSegDesc> {
        let k = stage.warps.len();
        assert!((1..=BWD_SEG_MAX_K).contains(&k));
        let mut stream: Vec<u16> = Vec::new();
        let mut list_offset = [0u16; BWD_SEG_MAX_K + 1];
        for (w, warp) in stage.warps.iter().enumerate() {
            list_offset[w] = stream.len() as u16;
            for term in warp {
                match term {
                    Term::T { class, coeff, a, b } => {
                        stream.push((*class << LEAN_CLASS_SHIFT) | *coeff);
                        stream.push(*a);
                        stream.push(*b);
                    }
                    Term::G {
                        core,
                        flags,
                        members,
                    } => {
                        assert!(members.len() >= 2, "{}: a group needs members", self.label);
                        stream.push((LEAN_CONT_GROUP_HEADER_CLASS << LEAN_CLASS_SHIFT) | *core);
                        stream.push(members.len() as u16);
                        stream.push(*flags);
                        for (class, immediate, a, b) in members {
                            stream.push((*class << LEAN_CLASS_SHIFT) | *immediate);
                            stream.push(*a);
                            stream.push(*b);
                        }
                    }
                }
            }
        }
        list_offset[k] = stream.len() as u16;

        // SAFETY: `BwdSegDesc` is plain `repr(C)` data, so zero is valid for
        // every field and initializes its padding deterministically.
        let mut desc: Box<BwdSegDesc> = unsafe { zeroed_box() };
        desc.program[..stream.len()].copy_from_slice(&stream);
        desc.list_offset = list_offset;
        desc.k = k as u16;
        desc.num_foldable = stage.fold_order.len() as u16;
        for (entry, &index) in desc.fold_source.iter_mut().zip(stage.fold_order.iter()) {
            *entry = index as u16;
        }
        for (record, source) in desc.source.iter_mut().zip(stage.sources.iter()) {
            *record = BwdSegSourceRecord {
                src: source.src,
                cache: source.cache.unwrap_or(BWD_SEG_ADDR_NONE),
                class: source.class,
                delta: source.delta,
            };
        }
        for (entry, slot) in desc.slot.iter_mut().zip(self.slots.iter()) {
            *entry = BwdSegAddrSlot {
                base: slot.base(),
                log2_stride: slot.log2_stride as u8,
                origin: slot.origin(),
                procedural_kind: slot.procedural_kind(),
                reserved: [0; 5],
            };
        }
        desc.c_init_coeff = BWD_SEG_C_INIT_NONE;
        for (entry, scalar) in desc.immediates.iter_mut().zip(self.immediates.iter()) {
            *entry = scalar.as_u32_raw_repr_reduced();
        }
        desc.eq_low = eq_low;
        desc.contributions = contributions;
        desc.eq_sizes = eq_sizes;
        desc.logical_rows = stage.rows as u32;
        desc
    }

    /// Checks the stage's invariants the harness itself depends on: a
    /// publication is exactly a folded source, and a base-field operand is
    /// never folded.
    fn check_stage(&self, stage: &Stage) {
        let mut claimed: BTreeSet<u16> = BTreeSet::new();
        for source in stage.sources.iter() {
            if let Some(cache) = source.cache {
                assert!(
                    claimed.insert(cache),
                    "{}: two sources publish into the same destination lane",
                    self.label
                );
            }
        }
        for (index, source) in stage.sources.iter().enumerate() {
            assert_eq!(
                source.cache.is_some(),
                stage.fold_order.contains(&index),
                "{}: source {index} publishes without being folded, or the other way round",
                self.label
            );
            if source.class == CLASS_BF_DIRECT || source.class == CLASS_PROCEDURAL_INLINE {
                assert!(
                    source.delta == 0 || source.cache.is_some(),
                    "{}: source {index} is read at depth zero but carries a delta",
                    self.label
                );
            }
            if source.class == CLASS_E4_DIRECT && source.cache.is_none() {
                assert_eq!(
                    source.delta, 0,
                    "{}: a direct E4 source is never folded",
                    self.label
                );
            }
            assert!(usize::from(source.delta) <= MAX_DELTA);
            if source.cache.is_none() {
                assert!(
                    usize::from(source.delta) <= 2,
                    "{}: an inline fold cannot exceed the publication threshold",
                    self.label
                );
            }
        }
    }

    fn run(&mut self, stage: &Stage, report: &mut Vec<String>) {
        self.check_stage(stage);
        let rows = stage.rows;
        assert!(rows > 0 && rows <= GKR_EQ_GROUP_TABLE_LEN);
        let warp = WARP_SIZE as usize;
        let grid = rows.div_ceil(warp);
        let low = rows.next_power_of_two().trailing_zeros();

        // A distinct eq weight per row, so the tile sums the kernel stores keep
        // every row's identity.
        let eq: Vec<E4> = (0..GKR_EQ_GROUP_TABLE_LEN)
            .map(|_| random_e4(&mut self.rng))
            .collect();
        let d_eq = upload_e4(self.context, &eq);
        let mut d_contributions = upload_e4(self.context, &vec![poison(); 2 * grid]);

        let desc = self.descriptor(
            stage,
            d_eq.as_ptr(),
            GkrEqSizes {
                high: [0; GKR_EQ_HIGH_SLOTS],
                low,
            },
            d_contributions.as_mut_ptr(),
        );
        if stage.r0 {
            launch_bwd_seg_r0(&desc, self.context).unwrap();
        } else {
            launch_bwd_seg_continuation(stage.round, &desc, self.context).unwrap();
        }
        self.context.get_exec_stream().synchronize().unwrap();

        let weights: Vec<Vec<E4>> = (0..=MAX_DELTA)
            .map(|delta| self.weights(delta, stage.round))
            .collect();

        // Every published fold, resolved into the destination mirrors first so
        // the reread oracle below sees the expected bytes rather than the
        // kernel's.
        let mut destinations: Vec<(usize, usize, usize)> = Vec::new();
        for &index in &stage.fold_order {
            let source = &stage.sources[index];
            let cache = source.cache.unwrap();
            let expected: Vec<E4> = (0..2 * rows)
                .map(|u| {
                    self.folded(
                        source.src,
                        source.delta,
                        u,
                        &weights[usize::from(source.delta)],
                    )
                })
                .collect();
            let slot = lane_slot(cache);
            let base = lane_column(cache) << self.slots[slot].log2_stride;
            match &mut self.slots[slot].store {
                Store::Ext(host, _) => host[base..base + 2 * rows].copy_from_slice(&expected),
                _ => panic!("{}: a publication destination must be E4", self.label),
            }
            destinations.push((slot, base, 2 * rows));
        }

        let mut checked: Vec<usize> = Vec::new();
        for (slot, base, live) in destinations.iter().copied() {
            let (host, device) = match &self.slots[slot].store {
                Store::Ext(host, device) => (host, device),
                _ => unreachable!(),
            };
            let from_gpu = download_e4(self.context, device);
            assert!(
                from_gpu[base..base + live].iter().all(|v| *v != poison()),
                "{} / {}: the publication left live destination cells unwritten",
                self.label,
                stage.name,
            );
            // A backing carries every column published into it, so compare the
            // whole allocation once: the poison outside the live ranges is the
            // overrun check.
            if checked.contains(&slot) {
                continue;
            }
            checked.push(slot);
            self.compare(
                &from_gpu,
                host,
                &format!("{} / {}: published slot {slot}", self.label, stage.name),
                report,
            );
        }

        let mut expected = vec![E4::ZERO; 2 * grid];
        for block in 0..grid {
            let mut sum_c0 = E4::ZERO;
            let mut sum_c2 = E4::ZERO;
            let last = ((block + 1) * warp).min(rows);
            for (row, eq_row) in eq.iter().enumerate().take(last).skip(block * warp) {
                let (c0, c2) = self.eval_row(stage, row, &weights);
                sum_c0 = add(sum_c0, mul(*eq_row, c0));
                sum_c2 = add(sum_c2, mul(*eq_row, c2));
            }
            expected[2 * block] = sum_c0;
            expected[2 * block + 1] = sum_c2;
        }
        let from_gpu = download_e4(self.context, &d_contributions);
        assert!(
            from_gpu.iter().all(|v| *v != poison()),
            "{} / {}: the executor stored no contribution",
            self.label,
            stage.name,
        );
        self.compare(
            &from_gpu,
            &expected,
            &format!("{} / {}: accumulator", self.label, stage.name),
            report,
        );
    }

    /// The claim `ab_backward_new_claims_linear_kernel` derives from a
    /// publication's two endpoint cells — the exact two E4 the final gather
    /// hands it, read from the destination backing at the column base.
    fn linear_claim(&self, cache: u16, r_last: E4) -> E4 {
        let slot = &self.slots[lane_slot(cache)];
        let base = lane_column(cache) << slot.log2_stride;
        let device = match &slot.store {
            Store::Ext(_, device) => device,
            _ => panic!("{}: a publication destination must be E4", self.label),
        };
        let d_challenge = upload_e4(self.context, &[r_last]);
        let mut d_claim: DeviceAllocation<E4> =
            self.context.alloc(1, AllocationPlacement::Top).unwrap();
        crate::gkr_ops::backward_new_claims_linear(
            &device[base..base + 2],
            &d_challenge[..],
            &mut d_claim[..],
            self.context.get_exec_stream(),
        )
        .unwrap();
        download_e4(self.context, &d_claim)[0]
    }

    fn compare(&self, from_gpu: &[E4], expected: &[E4], what: &str, report: &mut Vec<String>) {
        assert_eq!(from_gpu.len(), expected.len(), "{what}: length");
        let differing = from_gpu
            .iter()
            .zip(expected.iter())
            .filter(|(g, e)| g != e)
            .count();
        if differing == 0 {
            return;
        }
        let indices: Vec<usize> = from_gpu
            .iter()
            .zip(expected.iter())
            .enumerate()
            .filter_map(|(i, (g, e))| (g != e).then_some(i))
            .take(16)
            .collect();
        let first = indices[0];
        report.push(format!(
            "{what}: {differing}/{} entries differ at {indices:?}{}; first gpu {:?} expected {:?}",
            from_gpu.len(),
            if differing > indices.len() { ".." } else { "" },
            from_gpu[first],
            expected[first],
        ));
    }
}

// ── Cases ───────────────────────────────────────────────────────────────────

/// The R0 program over eight rows, where the two conventions diverge on the
/// endpoint pairing alone (every source sits at depth zero).
fn r0_delta_zero(context: &ProverContext, report: &mut Vec<String>) {
    let mut fixture = Fixture::new(context, "r0 depth zero", 0x5e_9a_00_02, 1);
    run_r0(&mut fixture, "r0 rows=8", 8, report);
}

/// A partial tile at R0: twenty rows over one block, the last twelve lanes dead.
fn r0_partial_tile(context: &ProverContext, report: &mut Vec<String>) {
    let mut fixture = Fixture::new(context, "r0 partial tile", 0x5e_9a_00_03, 1);
    run_r0(&mut fixture, "r0 rows=20", 20, report);
}

/// All five R0 term classes over base-field, procedural and E4 sources.
fn run_r0(fixture: &mut Fixture<'_>, name: &'static str, rows: usize, report: &mut Vec<String>) {
    let stride = (2 * rows).next_power_of_two().trailing_zeros();
    let base = fixture.add_bf(2, stride);
    let procedural = fixture.add_procedural();
    let ext = fixture.add_e4(2, stride);

    let stage = Stage {
        name,
        r0: true,
        rows,
        round: 0,
        sources: vec![
            Src {
                src: fixture.lane(base, 1),
                cache: None,
                class: CLASS_BF_DIRECT,
                delta: 0,
            },
            Src {
                src: fixture.lane(procedural, 0),
                cache: None,
                class: CLASS_PROCEDURAL_INLINE,
                delta: 0,
            },
            Src {
                src: fixture.lane(ext, 1),
                cache: None,
                class: CLASS_E4_DIRECT,
                delta: 0,
            },
        ],
        fold_order: Vec::new(),
        warps: vec![vec![
            unary(r0_class(0), 3, 0),
            unary(r0_class(1), 4, 2),
            // A base-field window read through the E4 resolver: depth zero, so
            // the lift.
            unary(r0_class(1), 5, 0),
            binary(r0_class(2), 6, 0, 1),
            binary(r0_class(3), 7, 1, 2),
            binary(r0_class(4), 8, 2, 2),
        ]],
    };
    fixture.run(&stage, report);
}

/// A depth-one publication out of a base-field backing, plus a depth-one inline
/// fold and a direct read.
fn continuation_depth1(context: &ProverContext, report: &mut Vec<String>) {
    let mut fixture = Fixture::new(context, "continuation depth one", 0x5e_9a_00_13, 3);
    let rows = 8usize;
    let base = fixture.add_bf(2, 6);
    let dest = fixture.add_dest(2, 4);
    let inline = fixture.add_bf(1, 6);
    let direct = fixture.add_e4(1, 4);

    let stage = Stage {
        name: "continuation rows=8 delta=1",
        r0: false,
        rows,
        round: 2,
        sources: vec![
            Src {
                src: fixture.lane(base, 1),
                cache: Some(fixture.lane(dest, 1)),
                class: CLASS_E4_DIRECT,
                delta: 1,
            },
            Src {
                src: fixture.lane(inline, 0),
                cache: None,
                class: CLASS_BF_INLINE_D1,
                delta: 1,
            },
            Src {
                src: fixture.lane(direct, 0),
                cache: None,
                class: CLASS_E4_DIRECT,
                delta: 0,
            },
        ],
        fold_order: vec![0],
        warps: vec![vec![
            unary(ext_class(0), 3, 0),
            binary(ext_class(1), 4, 1, 2),
            binary(ext_class(1), 5, 0, 1),
            Term::G {
                core: 6,
                flags: LEAN_GROUP_FLAG_C0 | LEAN_GROUP_FLAG_C2,
                members: vec![
                    (ext_class(0), ImmediateId::ONE.0, 1, SOURCE_NONE),
                    (ext_class(1), ImmediateId::NEG_ONE.0, 0, 2),
                    (ext_class(0), ImmediateId::RESERVED, 2, SOURCE_NONE),
                    (ext_class(0), ImmediateId::RESERVED + 1, 0, SOURCE_NONE),
                ],
            },
        ]],
    };
    fixture.run(&stage, report);
}

/// Depth-two publications out of an extension backing and out of a procedural
/// window, plus a depth-two inline fold, striped over three warps.
fn continuation_depth2(context: &ProverContext, report: &mut Vec<String>) {
    let mut fixture = Fixture::new(context, "continuation depth two", 0x5e_9a_00_14, 4);
    let rows = 8usize;
    let ext = fixture.add_e4(1, 6);
    let procedural = fixture.add_procedural();
    let dest = fixture.add_dest(2, 4);
    let inline = fixture.add_bf(1, 6);

    let stage = Stage {
        name: "continuation rows=8 delta=2",
        r0: false,
        rows,
        round: 3,
        sources: vec![
            Src {
                src: fixture.lane(ext, 0),
                cache: Some(fixture.lane(dest, 0)),
                class: CLASS_E4_DIRECT,
                delta: 2,
            },
            Src {
                src: fixture.lane(procedural, 0),
                cache: Some(fixture.lane(dest, 1)),
                class: CLASS_E4_DIRECT,
                delta: 2,
            },
            Src {
                src: fixture.lane(inline, 0),
                cache: None,
                class: CLASS_BF_INLINE_D2,
                delta: 2,
            },
        ],
        fold_order: vec![0, 1],
        warps: vec![
            vec![unary(ext_class(0), 3, 0)],
            vec![binary(ext_class(1), 4, 1, 2)],
            vec![
                binary(ext_class(1), 5, 0, 1),
                Term::G {
                    core: 6,
                    flags: LEAN_GROUP_FLAG_C2,
                    members: vec![
                        (ext_class(1), ImmediateId::ONE.0, 2, 2),
                        (ext_class(1), ImmediateId::RESERVED + 2, 0, 1),
                    ],
                },
            ],
        ],
    };
    fixture.run(&stage, report);
}

/// Depth-three publications — the deepest the prologue materializes — out of a
/// base-field and an extension backing.
fn continuation_depth3(context: &ProverContext, report: &mut Vec<String>) {
    let mut fixture = Fixture::new(context, "continuation depth three", 0x5e_9a_00_15, 4);
    let rows = 4usize;
    let base = fixture.add_bf(1, 6);
    let ext = fixture.add_e4(1, 6);
    let dest = fixture.add_dest(2, 3);

    let stage = Stage {
        name: "continuation rows=4 delta=3",
        r0: false,
        rows,
        round: 3,
        sources: vec![
            Src {
                src: fixture.lane(base, 0),
                cache: Some(fixture.lane(dest, 0)),
                class: CLASS_E4_DIRECT,
                delta: 3,
            },
            Src {
                src: fixture.lane(ext, 0),
                cache: Some(fixture.lane(dest, 1)),
                class: CLASS_E4_DIRECT,
                delta: 3,
            },
        ],
        fold_order: vec![0, 1],
        warps: vec![
            vec![unary(ext_class(0), 3, 0)],
            vec![binary(ext_class(1), 4, 0, 1)],
        ],
    };
    fixture.run(&stage, report);
}

/// A partial tile in the continuation regime: forty rows over two blocks, so
/// both the prologue's and the executor's clamped lanes are live.
fn continuation_partial_tile(context: &ProverContext, report: &mut Vec<String>) {
    let mut fixture = Fixture::new(context, "continuation partial tile", 0x5e_9a_00_16, 3);
    let rows = 40usize;
    let base = fixture.add_bf(1, 8);
    let dest = fixture.add_dest(1, 7);
    let direct = fixture.add_e4(1, 7);

    let stage = Stage {
        name: "continuation rows=40 delta=1",
        r0: false,
        rows,
        round: 2,
        sources: vec![
            Src {
                src: fixture.lane(base, 0),
                cache: Some(fixture.lane(dest, 0)),
                class: CLASS_E4_DIRECT,
                delta: 1,
            },
            Src {
                src: fixture.lane(direct, 0),
                cache: None,
                class: CLASS_E4_DIRECT,
                delta: 0,
            },
        ],
        fold_order: vec![0],
        warps: vec![
            vec![unary(ext_class(0), 3, 0)],
            vec![binary(ext_class(1), 4, 0, 1)],
        ],
    };
    fixture.run(&stage, report);
}

/// Two chained rounds: the second round's prologue folds what the first round
/// published, and its own publication is read back inside the same launch. The
/// first round's destination is compared cell by cell BEFORE the second launch,
/// so a wrong physical layout cannot cancel between the publication and the
/// reread; the second round's oracle then reads the EXPECTED intermediate
/// rather than the bytes the first launch produced.
fn continuation_chain(context: &ProverContext, report: &mut Vec<String>) {
    let mut fixture = Fixture::new(context, "continuation chain", 0x5e_9a_00_17, 4);
    let base = fixture.add_bf(1, 5);
    let middle = fixture.add_dest(1, 4);
    let last = fixture.add_dest(1, 3);

    let first = Stage {
        name: "chain round 2 rows=8 delta=1",
        r0: false,
        rows: 8,
        round: 2,
        sources: vec![Src {
            src: fixture.lane(base, 0),
            cache: Some(fixture.lane(middle, 0)),
            class: CLASS_E4_DIRECT,
            delta: 1,
        }],
        fold_order: vec![0],
        warps: vec![vec![
            unary(ext_class(0), 3, 0),
            binary(ext_class(1), 6, 0, 0),
        ]],
    };
    fixture.run(&first, report);

    let second = Stage {
        name: "chain round 3 rows=4 delta=1",
        r0: false,
        rows: 4,
        round: 3,
        sources: vec![Src {
            src: fixture.lane(middle, 0),
            cache: Some(fixture.lane(last, 0)),
            class: CLASS_E4_DIRECT,
            delta: 1,
        }],
        fold_order: vec![0],
        warps: vec![vec![
            unary(ext_class(0), 4, 0),
            binary(ext_class(1), 5, 0, 0),
        ]],
    };
    fixture.run(&second, report);
}

/// The producer boundary the final gather reads. At one row a publication
/// writes the two endpoint cells `[0, 1]` that
/// `ab_backward_new_claims_linear_kernel` consumes, and the endpoint bit sits
/// directly above the `delta` leaf coordinates: leaf index bit `j` carries
/// claim coordinate `round - delta + j` for `j = 0 ..= delta`, bit `delta`
/// being the endpoint the round's own challenge binds. A basis vector at leaf
/// `l` must therefore reach the consumer as the LSB weight product over the
/// bits of `l`.
fn final_evaluation_packing(context: &ProverContext, report: &mut Vec<String>) {
    for delta in [0, MAX_DELTA] {
        let round = delta as u32 + 1;
        let leaves = 2usize << delta;
        for hot in 0..leaves {
            let mut fixture = Fixture::new(
                context,
                "final-evaluation packing",
                0x5e_9a_00_20 + delta as u64,
                round as usize + 1,
            );
            let source = fixture.add_e4_basis(1 + delta as u32, hot);
            let dest = fixture.add_dest(1, 1);
            let cache = fixture.lane(dest, 0);
            let stage = Stage {
                name: "final round rows=1",
                r0: false,
                rows: 1,
                round,
                sources: vec![Src {
                    src: fixture.lane(source, 0),
                    cache: Some(cache),
                    class: CLASS_E4_DIRECT,
                    delta: delta as u8,
                }],
                fold_order: vec![0],
                warps: vec![vec![unary(ext_class(0), 3, 0)]],
            };
            fixture.run(&stage, report);

            let r_last = fixture.claim[round as usize];
            let claim = fixture.linear_claim(cache, r_last);
            let mut expected = E4::ONE;
            for j in 0..=delta {
                let coordinate = fixture.claim[round as usize - delta + j];
                expected = mul(
                    expected,
                    if (hot >> j) & 1 == 1 {
                        coordinate
                    } else {
                        sub(E4::ONE, coordinate)
                    },
                );
            }
            if claim != expected {
                report.push(format!(
                    "final-evaluation packing delta={delta} leaf {hot}: the consumer read \
                     {claim:?}, expected the LSB weight product {expected:?}",
                ));
            }
        }
    }
}

#[test]
fn segmented_vm_matches_lsb_address_algebra() {
    let context = make_test_context(256, 64);
    let mut report: Vec<String> = Vec::new();

    r0_delta_zero(&context, &mut report);
    r0_partial_tile(&context, &mut report);
    continuation_depth1(&context, &mut report);
    continuation_depth2(&context, &mut report);
    continuation_depth3(&context, &mut report);
    continuation_partial_tile(&context, &mut report);
    continuation_chain(&context, &mut report);
    final_evaluation_packing(&context, &mut report);

    assert!(
        report.is_empty(),
        "the segmented VM does not follow the LSB-dense address algebra:\n{}",
        report.join("\n"),
    );
}
