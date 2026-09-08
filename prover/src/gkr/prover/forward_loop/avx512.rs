//! AVX-512 SoA fast paths of the forward (output-construction) relations
//! (BabyBear/Ext4 only, selected at runtime): the lookup fraction adds and
//! setup lookups over extension and base inputs, the unbalanced pairs, the
//! masked identity product, the pairwise products, the cache relations
//! (memory tuples compiled into affine base forms times challenge constants,
//! single-column range-check caches, vectorized lookup gathers), the lookup
//! expression materializations from the witness mappings, the inits /
//! teardowns tuple pairs and the base-layer product without caches. 16 rows
//! per block, limb-major, lazy extension products; every value is
//! byte-identical to the scalar kernels (canonical arithmetic). Below
//! [`VECTOR_MIN_ROWS`] rows the scalar path runs (the later stages are
//! tiny). Each scalar entry point checks [`enabled`] first and hands over.
//! The module only exists on `x86_64 + avx2` builds; the hooks are cfg-gated.

use crate::definitions::GKRExternalChallenges;
use crate::gkr::prover::sumcheck_loop::windowed_mode::avx512 as k;
use crate::gkr::prover::sumcheck_loop::windowed_mode::avx512::ExtPerm;
use crate::gkr::sumcheck::access_and_fold::{BaseFieldPoly, ExtensionFieldPoly, GKRStorage};
use crate::gkr::sumcheck::evaluation_kernels::GKRInputs;
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use core::arch::x86_64::*;
use core::mem::MaybeUninit;
use cs::definitions::gkr::{
    AddressSpaceType, RamWordRepresentation, SingleColumnLookupRelation, VectorLookupRelation,
    DECODER_LOOKUP_FORMAL_SET_INDEX,
};
use cs::definitions::{
    GKRAddress, VirtualSetupPoly, PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX as ADDR_HIGH,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX as ADDR_LOW,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX as TS_HIGH,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX as TS_LOW,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX as VAL_HIGH,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX as VAL_LOW,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRCircuitArtifact, InitsOrTeardownsTimestampAndValue, SpecialMemoryContributionRelation,
};
use field::{Field, FieldExtension, PrimeField};
use std::alloc::Global;
use worker::Worker;

type BF = BabyBearField;
type BE = BabyBearExt4;
type Limbs = [__m512i; 4];

pub const VECTOR_MIN_ROWS: usize = 1 << 12;

pub fn enabled<F: PrimeField, E: Field>(trace_len: usize) -> bool {
    core::any::type_name::<F>() == core::any::type_name::<BF>()
        && core::any::type_name::<E>() == core::any::type_name::<BE>()
        && trace_len >= VECTOR_MIN_ROWS
        && trace_len % 16 == 0
        && is_x86_feature_detected!("avx512f")
}

// ---------------------------------------------------------------------------
// primitives
// ---------------------------------------------------------------------------

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn ld_ext16(p: *const BE, row0: usize, xp: &ExtPerm) -> Limbs {
    let z: [__m512i; 4] =
        core::array::from_fn(|i| _mm512_loadu_si512(p.add(row0 + 4 * i) as *const __m512i));
    k::transpose_ext16_vecs(&z, xp)
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn st_ext16(v: &Limbs, p: *mut BE, row0: usize, xp: &ExtPerm) {
    k::store_ext16_out(v, p.add(row0), xp, k::nt_stores())
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn ld_base16(p: *const BF, row0: usize) -> __m512i {
    k::ld(p.add(row0) as *const u32)
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn ld_u32x16(p: *const u32, row0: usize) -> __m512i {
    k::ld(p.add(row0))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn ld_u16x16(p: *const u16, row0: usize) -> __m512i {
    _mm512_cvtepu16_epi32(_mm256_loadu_si256(p.add(row0) as *const __m256i))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn add_base(v: &Limbs, b: __m512i) -> Limbs {
    [k::add16(v[0], b), v[1], v[2], v[3]]
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn add4(a: &Limbs, b: &Limbs) -> Limbs {
    core::array::from_fn(|l| k::add16(a[l], b[l]))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn sub4(a: &Limbs, b: &Limbs) -> Limbs {
    core::array::from_fn(|l| k::sub16(a[l], b[l]))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn mul_base(v: &Limbs, b: __m512i) -> Limbs {
    core::array::from_fn(|l| k::mont_mul16(v[l], b))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn bcast4(l: &[u32; 4]) -> Limbs {
    [k::bc32(l[0]), k::bc32(l[1]), k::bc32(l[2]), k::bc32(l[3])]
}
/// `mask ? a : b` per limb.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn select4(m: __mmask16, a: &Limbs, b: &Limbs) -> Limbs {
    core::array::from_fn(|l| _mm512_mask_blend_epi32(m, b[l], a[l]))
}
/// `table[idx]` for 16 extension entries, limb-major.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn gather_ext16(table: *const BE, idx: __m512i) -> Limbs {
    let i4 = _mm512_slli_epi32::<2>(idx);
    let t = table as *const i32;
    core::array::from_fn(|l| _mm512_i32gather_epi32::<4>(i4, t.add(l)))
}
/// `table.get(row).unwrap_or(ZERO)` for 16 rows (the setup column of a
/// lookup: the table itself, zero-padded to the trace).
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn table_row16(table: *const BE, len: usize, row0: usize, xp: &ExtPerm) -> Limbs {
    if row0 + 16 <= len {
        return ld_ext16(table, row0, xp);
    }
    let mut tmp = [BE::ZERO; 16];
    for i in 0..16 {
        if row0 + i < len {
            tmp[i] = *table.add(row0 + i);
        }
    }
    ld_ext16(tmp.as_ptr(), 0, xp)
}
/// Boolean mask of a 0/1 base column (`as_boolean` compares with ONE).
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn bool_mask16(v: __m512i) -> __mmask16 {
    _mm512_cmpeq_epi32_mask(v, k::bc32(one_raw()))
}

fn one_raw() -> u32 {
    BF::ONE.raw_u32_value()
}
/// R^2 mod P as a raw value: `mont_mul(v, R2) = v * R mod P = BabyBearField::new(v)`.
fn mont_r2() -> u32 {
    BF::new(BF::new(1).raw_u32_value()).raw_u32_value()
}
fn limbs<E: Field>(e: &E) -> [u32; 4] {
    debug_assert_eq!(core::mem::size_of::<E>(), 16);
    unsafe { core::ptr::read(e as *const E as *const [u32; 4]) }
}
fn ext_ptr<E>(s: &[E]) -> usize {
    s.as_ptr() as usize
}
fn base_ptr<F>(s: &[F]) -> usize {
    s.as_ptr() as usize
}

/// Run `f(row0)` over every 16-row block, split over the worker.
fn run_blocks(trace_len: usize, worker: &Worker, f: impl Fn(usize) + Sync) {
    let blocks = trace_len / 16;
    worker.scope(blocks, |scope, geometry| {
        for idx in 0..geometry.len() {
            let start = geometry.get_chunk_start_pos(idx);
            let size = geometry.get_chunk_size(idx);
            let f = &f;
            Worker::smart_spawn(scope, idx == geometry.len() - 1, move |_| {
                for b in start..start + size {
                    f(b * 16);
                }
                // non-temporal stores: drain the write-combining buffers before
                // the outputs are handed to other threads
                unsafe { _mm_sfence() };
            });
        }
    });
}

/// The output buffers must be 16-byte aligned for the non-temporal stores
/// (every allocator hands out 16-byte aligned blocks of these sizes).
fn check_out_alignment(ptr: usize) {
    assert!(
        ptr % 16 == 0 || !k::nt_stores(),
        "forward output buffer is not 16-byte aligned"
    );
}

/// Raw pointers of the round-0 values of base / extension inputs.
fn fetch_ptrs<F: PrimeField, E: FieldExtension<F> + Field>(
    storage: &mut GKRStorage<F, E>,
    base: Vec<GKRAddress>,
    ext: Vec<GKRAddress>,
) -> (Vec<usize>, Vec<usize>) {
    let gi = GKRInputs {
        inputs_in_base: base,
        inputs_in_extension: ext,
        outputs_in_base: Vec::new(),
        outputs_in_extension: Vec::new(),
    };
    let s = storage.get_for_sumcheck_round_0(&gi);
    (
        s.base_field_inputs
            .iter()
            .map(|p| p.current_values().as_ptr() as usize)
            .collect(),
        s.extension_field_inputs
            .iter()
            .map(|p| p.current_values().as_ptr() as usize)
            .collect(),
    )
}

/// Outputs allocated from the storage pool, filled by `fill(dst_ptrs)`,
/// inserted at the layer.
fn with_outputs<F: PrimeField, E: FieldExtension<F> + Field>(
    storage: &mut GKRStorage<F, E>,
    outputs: &[GKRAddress],
    expected_output_layer: usize,
    trace_len: usize,
    fill: impl FnOnce(&[usize]),
) {
    let mut dsts: Vec<Box<[MaybeUninit<E>]>> = outputs
        .iter()
        .map(|_| storage.alloc_ext_uninit(trace_len))
        .collect();
    let ptrs: Vec<usize> = dsts.iter_mut().map(|d| d.as_mut_ptr() as usize).collect();
    ptrs.iter().for_each(|&p| check_out_alignment(p));
    fill(&ptrs);
    for (addr, dst) in outputs.iter().zip(dsts.into_iter()) {
        addr.assert_as_layer(expected_output_layer);
        storage.insert_extension_at_layer(
            expected_output_layer,
            *addr,
            ExtensionFieldPoly::new(unsafe { dst.assume_init() }),
        );
    }
}

/// One pooled extension buffer filled by `fill(dst_ptr)`.
fn make_ext<F: PrimeField, E: FieldExtension<F> + Field>(
    storage: &GKRStorage<F, E>,
    trace_len: usize,
    fill: impl FnOnce(usize),
) -> Box<[E]> {
    let mut dst = storage.alloc_ext_uninit(trace_len);
    check_out_alignment(dst.as_mut_ptr() as usize);
    fill(dst.as_mut_ptr() as usize);
    unsafe { dst.assume_init() }
}

// ---------------------------------------------------------------------------
// affine plans: additive + sum_k ch_k (x) (sum_i c_i col_i + const)
// ---------------------------------------------------------------------------

/// One term: an affine base form (raw Montgomery coefficients over base
/// column pointers plus a raw constant), optionally multiplied by an
/// extension challenge (`None`: added to limb 0).
struct Term {
    ch: Option<[u32; 4]>,
    cols: Vec<(u32, usize)>,
    constant: u32,
}

struct Plan {
    additive: [u32; 4],
    terms: Vec<Term>,
}

impl Plan {
    fn new(additive: &BE) -> Self {
        Self {
            additive: limbs(additive),
            terms: Vec::new(),
        }
    }
    fn linear(&mut self, ch: &BE, cols: Vec<(u32, usize)>, constant: u32) {
        self.terms.push(Term {
            ch: Some(limbs(ch)),
            cols,
            constant,
        });
    }
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn eval_plan(plan: &Plan, row0: usize) -> Limbs {
    let one = one_raw();
    let mut acc = bcast4(&plan.additive);
    for term in plan.terms.iter() {
        let mut a = k::bc32(term.constant);
        for &(coeff, col) in term.cols.iter() {
            let v = ld_base16(col as *const BF, row0);
            a = k::add16(
                a,
                if coeff == one {
                    v
                } else {
                    k::mont_mul16(v, k::bc32(coeff))
                },
            );
        }
        match &term.ch {
            Some(c) => acc = add4(&acc, &mul_base(&bcast4(c), a)),
            None => acc[0] = k::add16(acc[0], a),
        }
    }
    acc
}

/// Mirror of `utils::evaluate_memory_query` as a plan over the base-layer
/// memory column pointers; `None` for the shapes that need integer
/// arithmetic on reduced values (dynamic offsets) or the generic address
/// form.
fn compile_mem_query(
    rel: &SpecialMemoryContributionRelation,
    ch: &GKRExternalChallenges<BF, BE>,
    mem_cols: &[usize],
) -> Option<Plan> {
    let lin = &ch.permutation_argument_linearization_challenges;
    let one = one_raw();
    let mut additive = ch.permutation_argument_additive_part;
    let mut terms: Vec<Term> = Vec::new();
    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            additive.add_assign_base(&BF::from_u32_unchecked(c));
        }
        CompiledAddressSpaceRelationStrict::IsRam(offset) => terms.push(Term {
            ch: None,
            cols: vec![(one, mem_cols[offset])],
            constant: 0,
        }),
        CompiledAddressSpaceRelationStrict::IsRegister(offset) => terms.push(Term {
            ch: None,
            cols: vec![(BF::MINUS_ONE.raw_u32_value(), mem_cols[offset])],
            constant: one,
        }),
    }
    let mut plan = Plan {
        additive: [0; 4],
        terms,
    };
    match &rel.address {
        &CompiledAddressStrict::ConstantU16(c) => {
            let mut t = lin[ADDR_LOW];
            t.mul_assign_by_base(&BF::from_u32_unchecked(c as u32));
            additive.add_assign(&t);
        }
        &CompiledAddressStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            let mut t = lin[ADDR_LOW];
            t.mul_assign_by_base(&BF::from_u32_unchecked(c));
            additive.add_assign(&t);
        }
        &CompiledAddressStrict::U16Space(offset) => {
            plan.linear(&lin[ADDR_LOW], vec![(one, mem_cols[offset])], 0)
        }
        &CompiledAddressStrict::U32Space([low, high]) => {
            plan.linear(&lin[ADDR_LOW], vec![(one, mem_cols[low])], 0);
            plan.linear(&lin[ADDR_HIGH], vec![(one, mem_cols[high])], 0);
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            if low_dynamic_offset.is_some() {
                return None;
            }
            plan.linear(
                &lin[ADDR_LOW],
                vec![(one, mem_cols[*low_base])],
                BF::from_u32_unchecked(*low_offset).raw_u32_value(),
            );
            plan.linear(&lin[ADDR_HIGH], vec![(one, mem_cols[*high])], 0);
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => return None,
    }
    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            plan.linear(
                &lin[TS_LOW],
                vec![(one, mem_cols[ts[0]])],
                BF::from_u32_unchecked(rel.timestamp_offset as u32).raw_u32_value(),
            );
            plan.linear(&lin[TS_HIGH], vec![(one, mem_cols[ts[1]])], 0);
        }
    }
    match rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(rv) => {
            plan.linear(&lin[VAL_LOW], vec![(one, mem_cols[rv[0]])], 0);
            plan.linear(&lin[VAL_HIGH], vec![(one, mem_cols[rv[1]])], 0);
        }
        RamWordRepresentation::U8Limbs(b) => {
            let shift = BF::from_u32_unchecked(1u32 << 8).raw_u32_value();
            plan.linear(
                &lin[VAL_LOW],
                vec![(one, mem_cols[b[0]]), (shift, mem_cols[b[1]])],
                0,
            );
            plan.linear(
                &lin[VAL_HIGH],
                vec![(one, mem_cols[b[2]]), (shift, mem_cols[b[3]])],
                0,
            );
        }
    }
    plan.additive = limbs(&additive);
    Some(plan)
}

/// Mirror of `inits_and_teardowns::evaluate_init` / `evaluate_teardown`.
fn compile_init_or_teardown(
    ch: &GKRExternalChallenges<BF, BE>,
    address_high_bits: u32,
    high_bits_offset: u32,
    teardown: Option<([usize; 2], [usize; 2])>,
    mem_cols: &[usize],
    address_low: usize,
    address_high: usize,
) -> Plan {
    let lin = &ch.permutation_argument_linearization_challenges;
    let one = one_raw();
    let mut additive = ch.permutation_argument_additive_part;
    additive.add_assign_base(&BF::from_u32_unchecked(AddressSpaceType::RAM as u32));
    let mut plan = Plan::new(&additive);
    plan.linear(&lin[ADDR_LOW], vec![(one, address_low)], 0);
    plan.linear(
        &lin[ADDR_HIGH],
        vec![(one, address_high)],
        BF::from_u32_unchecked(address_high_bits << high_bits_offset).raw_u32_value(),
    );
    if let Some((timestamp, value)) = teardown {
        plan.linear(&lin[TS_LOW], vec![(one, mem_cols[timestamp[0]])], 0);
        plan.linear(&lin[TS_HIGH], vec![(one, mem_cols[timestamp[1]])], 0);
        plan.linear(&lin[VAL_LOW], vec![(one, mem_cols[value[0]])], 0);
        plan.linear(&lin[VAL_HIGH], vec![(one, mem_cols[value[1]])], 0);
    }
    plan
}

fn mem_col_ptrs<F: PrimeField, E: FieldExtension<F> + Field>(
    storage: &GKRStorage<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
) -> Vec<usize> {
    (0..compiled_circuit.memory_layout.total_width)
        .map(|i| base_ptr(storage.get_base_layer_mem(i)))
        .collect()
}

fn challenges_bb<F: PrimeField, E: FieldExtension<F> + Field>(
    ch: &GKRExternalChallenges<F, E>,
) -> &GKRExternalChallenges<BF, BE> {
    unsafe { &*(ch as *const GKRExternalChallenges<F, E> as *const _) }
}

// ---------------------------------------------------------------------------
// block kernels
// ---------------------------------------------------------------------------

/// a/b + c/d -> (a d + c b), (b d); ext [a, b, c, d]
#[target_feature(enable = "avx512f")]
unsafe fn lookup_pair_block(src: [usize; 4], dst: [usize; 2], row0: usize) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let [a, b, c, d]: [Limbs; 4] =
        core::array::from_fn(|i| ld_ext16(src[i] as *const BE, row0, &xp));
    let num = add4(
        &k::soa_ext_mul_lazy(&a, &d, r11),
        &k::soa_ext_mul_lazy(&c, &b, r11),
    );
    let den = k::soa_ext_mul_lazy(&b, &d, r11);
    st_ext16(&num, dst[0] as *mut BE, row0, &xp);
    st_ext16(&den, dst[1] as *mut BE, row0, &xp);
}

/// 1/(b+g) + 1/(d+g) -> (B + D), (B D); base [b, d]
#[target_feature(enable = "avx512f")]
unsafe fn lookup_base_pair_block(src: [usize; 2], dst: [usize; 2], g: &[u32; 4], row0: usize) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let gv = bcast4(g);
    let bb = add_base(&gv, ld_base16(src[0] as *const BF, row0));
    let dd = add_base(&gv, ld_base16(src[1] as *const BF, row0));
    st_ext16(&add4(&bb, &dd), dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&bb, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// 1/(b+g) + 1/(d+g) over extension inputs; ext [b, d]
#[target_feature(enable = "avx512f")]
unsafe fn lookup_ext_pair_block(src: [usize; 2], dst: [usize; 2], g: &[u32; 4], row0: usize) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let gv = bcast4(g);
    let bb = add4(&ld_ext16(src[0] as *const BE, row0, &xp), &gv);
    let dd = add4(&ld_ext16(src[1] as *const BE, row0, &xp), &gv);
    st_ext16(&add4(&bb, &dd), dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&bb, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// a/b + 1/(d+g) -> (a D + b), (b D); base remainder d, ext [a, b]
#[target_feature(enable = "avx512f")]
unsafe fn unbalanced_base_block(
    rem: usize,
    ab: [usize; 2],
    dst: [usize; 2],
    g: &[u32; 4],
    row0: usize,
) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let dd = add_base(&bcast4(g), ld_base16(rem as *const BF, row0));
    let a = ld_ext16(ab[0] as *const BE, row0, &xp);
    let b = ld_ext16(ab[1] as *const BE, row0, &xp);
    let num = add4(&k::soa_ext_mul_lazy(&a, &dd, r11), &b);
    st_ext16(&num, dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&b, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// a/b + 1/(d+g) with an extension remainder d; ext [a, b, d]
#[target_feature(enable = "avx512f")]
unsafe fn unbalanced_ext_block(src: [usize; 3], dst: [usize; 2], g: &[u32; 4], row0: usize) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let a = ld_ext16(src[0] as *const BE, row0, &xp);
    let b = ld_ext16(src[1] as *const BE, row0, &xp);
    let dd = add4(&ld_ext16(src[2] as *const BE, row0, &xp), &bcast4(g));
    let num = add4(&k::soa_ext_mul_lazy(&a, &dd, r11), &b);
    st_ext16(&num, dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&b, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// 1/(b+g) - c/(d+g) -> (D - c B), (B D); base [b, c, d]
#[target_feature(enable = "avx512f")]
unsafe fn base_minus_mult_block(src: [usize; 3], dst: [usize; 2], g: &[u32; 4], row0: usize) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let gv = bcast4(g);
    let bb = add_base(&gv, ld_base16(src[0] as *const BF, row0));
    let c = ld_base16(src[1] as *const BF, row0);
    let dd = add_base(&gv, ld_base16(src[2] as *const BF, row0));
    let num = sub4(&dd, &mul_base(&bb, c));
    st_ext16(&num, dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&bb, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// 1/(b+g) - c/(d+g) with extension b, d and base multiplicity c
#[target_feature(enable = "avx512f")]
unsafe fn ext_minus_mult_block(
    c: usize,
    bd: [usize; 2],
    dst: [usize; 2],
    g: &[u32; 4],
    row0: usize,
) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let gv = bcast4(g);
    let bb = add4(&ld_ext16(bd[0] as *const BE, row0, &xp), &gv);
    let dd = add4(&ld_ext16(bd[1] as *const BE, row0, &xp), &gv);
    let cv = ld_base16(c as *const BF, row0);
    let num = sub4(&dd, &mul_base(&bb, cv));
    st_ext16(&num, dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&bb, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// a/(b+g) - c/(d+g) -> (a D - c B), (B D); base [a, c], ext [b, d]
#[target_feature(enable = "avx512f")]
unsafe fn masked_lookup_setup_block(
    ac: [usize; 2],
    bd: [usize; 2],
    dst: [usize; 2],
    g: &[u32; 4],
    row0: usize,
) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let gv = bcast4(g);
    let a = ld_base16(ac[0] as *const BF, row0);
    let c = ld_base16(ac[1] as *const BF, row0);
    let bb = add4(&ld_ext16(bd[0] as *const BE, row0, &xp), &gv);
    let dd = add4(&ld_ext16(bd[1] as *const BE, row0, &xp), &gv);
    let num = sub4(&mul_base(&dd, a), &mul_base(&bb, c));
    st_ext16(&num, dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&bb, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// (val - 1) mask + 1; base mask, ext val
#[target_feature(enable = "avx512f")]
unsafe fn mask_identity_block(mask: usize, val: usize, dst: usize, row0: usize) {
    let xp = ExtPerm::new();
    let one = k::bc32(one_raw());
    let m = ld_base16(mask as *const BF, row0);
    let mut v = ld_ext16(val as *const BE, row0, &xp);
    v[0] = k::sub16(v[0], one);
    v = mul_base(&v, m);
    v[0] = k::add16(v[0], one);
    st_ext16(&v, dst as *mut BE, row0, &xp);
}

/// a b over extension inputs
#[target_feature(enable = "avx512f")]
unsafe fn pairwise_block(src: [usize; 2], dst: usize, row0: usize) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let a = ld_ext16(src[0] as *const BE, row0, &xp);
    let b = ld_ext16(src[1] as *const BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&a, &b, r11), dst as *mut BE, row0, &xp);
}

/// plan(row) into an extension poly
#[target_feature(enable = "avx512f")]
unsafe fn plan_block(plan: &Plan, dst: usize, row0: usize) {
    let xp = ExtPerm::new();
    let v = eval_plan(plan, row0);
    st_ext16(&v, dst as *mut BE, row0, &xp);
}

/// plan_l(row) * plan_r(row)
#[target_feature(enable = "avx512f")]
unsafe fn plan_product_block(pl: &Plan, pr: &Plan, dst: usize, row0: usize) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let a = eval_plan(pl, row0);
    let b = eval_plan(pr, row0);
    st_ext16(&k::soa_ext_mul_lazy(&a, &b, r11), dst as *mut BE, row0, &xp);
}

/// Montgomery form of the u16 / u32 range-check mapping (a base cache).
#[target_feature(enable = "avx512f")]
unsafe fn single_column_block<const U16: bool>(map: usize, dst: usize, r2: u32, row0: usize) {
    let v = if U16 {
        ld_u16x16(map as *const u16, row0)
    } else {
        ld_u32x16(map as *const u32, row0)
    };
    let out = k::mont_mul16(v, k::bc32(r2));
    if k::nt_stores() {
        k::st_nt16((dst as *mut u32).add(row0), out);
    } else {
        k::st((dst as *mut u32).add(row0), out);
    }
}

/// 1/(m1+g) + 1/(m2+g) from two range-check mappings
#[target_feature(enable = "avx512f")]
unsafe fn range_check_pair_block<const U16: bool>(
    maps: [usize; 2],
    dst: [usize; 2],
    g: &[u32; 4],
    r2: u32,
    row0: usize,
) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let r2v = k::bc32(r2);
    let gv = bcast4(g);
    let load = |p: usize| {
        if U16 {
            ld_u16x16(p as *const u16, row0)
        } else {
            ld_u32x16(p as *const u32, row0)
        }
    };
    let lhs = add_base(&gv, k::mont_mul16(load(maps[0]), r2v));
    let rhs = add_base(&gv, k::mont_mul16(load(maps[1]), r2v));
    st_ext16(&add4(&lhs, &rhs), dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&lhs, &rhs, r11), dst[1] as *mut BE, row0, &xp);
}

/// table[map[row]], optionally `pred ? table[map] : fill`. A pure gather:
/// 16-byte copies (AVX-512 gathers are slower than the copies here).
#[target_feature(enable = "avx512f")]
unsafe fn vector_lookup_block(
    table: usize,
    map: usize,
    pred: Option<(usize, [u32; 4])>,
    dst: usize,
    row0: usize,
) {
    let t = table as *const __m128i;
    let m = (map as *const u32).add(row0);
    let d = (dst as *mut __m128i).add(row0);
    let nt = k::nt_stores();
    let st = |q: *mut __m128i, v: __m128i| {
        if nt {
            _mm_stream_si128(q, v)
        } else {
            _mm_storeu_si128(q, v)
        }
    };
    match pred {
        None => {
            for i in 0..16 {
                st(d.add(i), _mm_loadu_si128(t.add(*m.add(i) as usize)));
            }
        }
        Some((p, fill)) => {
            let fv = _mm_loadu_si128(fill.as_ptr() as *const __m128i);
            let one = one_raw();
            let pp = (p as *const u32).add(row0);
            for i in 0..16 {
                let v = if *pp.add(i) == one {
                    _mm_loadu_si128(t.add(*m.add(i) as usize))
                } else {
                    fv
                };
                st(d.add(i), v);
            }
        }
    }
}

/// `dst = table` zero-padded to `dst.len()`, split over the worker; the
/// zero tail uses non-temporal 16-byte stores (no read-for-ownership
/// traffic, the buffers are at least 16-byte aligned).
pub fn fill_setup_column<E: Field>(dst: &mut [MaybeUninit<E>], table: &[E], worker: &Worker) {
    assert_eq!(core::mem::size_of::<E>(), 16);
    let n = dst.len();
    assert!(table.len() <= n);
    let (dp, tp, tl) = (dst.as_mut_ptr() as usize, table.as_ptr() as usize, table.len());
    worker.scope(n, |scope, geometry| {
        for idx in 0..geometry.len() {
            let start = geometry.get_chunk_start_pos(idx);
            let size = geometry.get_chunk_size(idx);
            Worker::smart_spawn(scope, idx == geometry.len() - 1, move |_| unsafe {
                let d = dp as *mut MaybeUninit<E>;
                let t = tp as *const E;
                let copy_end = (start + size).min(tl);
                if start < copy_end {
                    core::ptr::copy_nonoverlapping(
                        t.add(start),
                        d.add(start) as *mut E,
                        copy_end - start,
                    );
                }
                let z0 = start.max(tl);
                if z0 < start + size {
                    zero_nt(d.add(z0) as *mut u8, (start + size - z0) * 16);
                }
            });
        }
    });
}

unsafe fn zero_nt(p: *mut u8, bytes: usize) {
    if (p as usize) % 16 != 0 {
        core::ptr::write_bytes(p, 0, bytes);
        return;
    }
    let z = _mm_setzero_si128();
    let mut q = p;
    let end = p.add(bytes);
    while q < end {
        _mm_stream_si128(q as *mut __m128i, z);
        q = q.add(16);
    }
    _mm_sfence();
}

/// decoder lookup minus setup: b = (pred ? table[map] : fill) + g,
/// d = table[row] + g (zero past the table): (d pred - b mult), (b d)
#[target_feature(enable = "avx512f")]
unsafe fn decoder_minus_setup_block(
    table: (usize, usize),
    map: usize,
    pred: usize,
    mult: usize,
    fill: &[u32; 4],
    g: &[u32; 4],
    dst: [usize; 2],
    row0: usize,
) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let gv = bcast4(g);
    let idx = ld_u32x16(map as *const u32, row0);
    let pv = ld_base16(pred as *const BF, row0);
    let m = bool_mask16(pv);
    let looked = select4(m, &gather_ext16(table.0 as *const BE, idx), &bcast4(fill));
    let bb = add4(&looked, &gv);
    let dd = add4(&table_row16(table.0 as *const BE, table.1, row0, &xp), &gv);
    let mv = ld_base16(mult as *const BF, row0);
    let num = sub4(&mul_base(&dd, pv), &mul_base(&bb, mv));
    st_ext16(&num, dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&bb, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// 1/(table[m1]+g) + 1/(table[m2]+g)
#[target_feature(enable = "avx512f")]
unsafe fn expressions_pair_block(
    table: usize,
    maps: [usize; 2],
    g: &[u32; 4],
    dst: [usize; 2],
    row0: usize,
) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let gv = bcast4(g);
    let t = table as *const BE;
    let bb = add4(&gather_ext16(t, ld_u32x16(maps[0] as *const u32, row0)), &gv);
    let dd = add4(&gather_ext16(t, ld_u32x16(maps[1] as *const u32, row0)), &gv);
    st_ext16(&add4(&dd, &bb), dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&bb, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// a/b + 1/(table[map]+g) -> (a D + b), (b D); ext [a, b]
#[target_feature(enable = "avx512f")]
unsafe fn expressions_pair_with_remainder_block(
    table: usize,
    map: usize,
    ab: [usize; 2],
    g: &[u32; 4],
    dst: [usize; 2],
    row0: usize,
) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let dd = add4(
        &gather_ext16(table as *const BE, ld_u32x16(map as *const u32, row0)),
        &bcast4(g),
    );
    let a = ld_ext16(ab[0] as *const BE, row0, &xp);
    let b = ld_ext16(ab[1] as *const BE, row0, &xp);
    let num = add4(&k::soa_ext_mul_lazy(&dd, &a, r11), &b);
    st_ext16(&num, dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&b, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

/// 1/(table[map]+g) - mult/(table[row]+g) -> (D - mult B), (B D)
#[target_feature(enable = "avx512f")]
unsafe fn expression_minus_setup_block(
    table: (usize, usize),
    map: usize,
    mult: usize,
    g: &[u32; 4],
    dst: [usize; 2],
    row0: usize,
) {
    let xp = ExtPerm::new();
    let r11 = k::r11v();
    let gv = bcast4(g);
    let bb = add4(
        &gather_ext16(table.0 as *const BE, ld_u32x16(map as *const u32, row0)),
        &gv,
    );
    let dd = add4(&table_row16(table.0 as *const BE, table.1, row0, &xp), &gv);
    let mv = ld_base16(mult as *const BF, row0);
    let num = sub4(&dd, &mul_base(&bb, mv));
    st_ext16(&num, dst[0] as *mut BE, row0, &xp);
    st_ext16(&k::soa_ext_mul_lazy(&bb, &dd, r11), dst[1] as *mut BE, row0, &xp);
}

// ---------------------------------------------------------------------------
// cores over raw slices (BabyBear types): the entry points and the parity
// tests share these
// ---------------------------------------------------------------------------

pub(crate) mod core_ops {
    use super::*;

    pub(crate) fn lookup_pair(src: [usize; 4], dst: [usize; 2], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { lookup_pair_block(src, dst, r) });
    }
    pub(crate) fn lookup_base_pair(src: [usize; 2], dst: [usize; 2], g: [u32; 4], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { lookup_base_pair_block(src, dst, &g, r) });
    }
    pub(crate) fn lookup_ext_pair(src: [usize; 2], dst: [usize; 2], g: [u32; 4], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { lookup_ext_pair_block(src, dst, &g, r) });
    }
    pub(crate) fn unbalanced_base(rem: usize, ab: [usize; 2], dst: [usize; 2], g: [u32; 4], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { unbalanced_base_block(rem, ab, dst, &g, r) });
    }
    pub(crate) fn unbalanced_ext(src: [usize; 3], dst: [usize; 2], g: [u32; 4], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { unbalanced_ext_block(src, dst, &g, r) });
    }
    pub(crate) fn base_minus_mult(src: [usize; 3], dst: [usize; 2], g: [u32; 4], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { base_minus_mult_block(src, dst, &g, r) });
    }
    pub(crate) fn ext_minus_mult(c: usize, bd: [usize; 2], dst: [usize; 2], g: [u32; 4], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { ext_minus_mult_block(c, bd, dst, &g, r) });
    }
    pub(crate) fn masked_lookup_setup(ac: [usize; 2], bd: [usize; 2], dst: [usize; 2], g: [u32; 4], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { masked_lookup_setup_block(ac, bd, dst, &g, r) });
    }
    pub(crate) fn mask_identity(mask: usize, val: usize, dst: usize, n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { mask_identity_block(mask, val, dst, r) });
    }
    pub(crate) fn pairwise(src: [usize; 2], dst: usize, n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { pairwise_block(src, dst, r) });
    }
    pub(crate) fn single_column<const U16: bool>(map: usize, dst: usize, n: usize, w: &Worker) {
        let r2 = mont_r2();
        run_blocks(n, w, |r| unsafe { single_column_block::<U16>(map, dst, r2, r) });
    }
    pub(crate) fn range_check_pair<const U16: bool>(maps: [usize; 2], dst: [usize; 2], g: [u32; 4], n: usize, w: &Worker) {
        let r2 = mont_r2();
        run_blocks(n, w, |r| unsafe { range_check_pair_block::<U16>(maps, dst, &g, r2, r) });
    }
    pub(crate) fn vector_lookup(table: usize, map: usize, pred: Option<(usize, [u32; 4])>, dst: usize, n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { vector_lookup_block(table, map, pred, dst, r) });
    }
    pub(crate) fn decoder_minus_setup(table: (usize, usize), map: usize, pred: usize, mult: usize, fill: [u32; 4], g: [u32; 4], dst: [usize; 2], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { decoder_minus_setup_block(table, map, pred, mult, &fill, &g, dst, r) });
    }
    pub(crate) fn expressions_pair(table: usize, maps: [usize; 2], g: [u32; 4], dst: [usize; 2], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { expressions_pair_block(table, maps, &g, dst, r) });
    }
    pub(crate) fn expressions_pair_with_remainder(table: usize, map: usize, ab: [usize; 2], g: [u32; 4], dst: [usize; 2], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { expressions_pair_with_remainder_block(table, map, ab, &g, dst, r) });
    }
    pub(crate) fn expression_minus_setup(table: (usize, usize), map: usize, mult: usize, g: [u32; 4], dst: [usize; 2], n: usize, w: &Worker) {
        run_blocks(n, w, |r| unsafe { expression_minus_setup_block(table, map, mult, &g, dst, r) });
    }
}

// ---------------------------------------------------------------------------
// entry points (generic plumbing around the cores)
// ---------------------------------------------------------------------------

/// AggregateLookupRationalPair
pub fn lookup_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [[GKRAddress; 2]; 2],
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    worker: &Worker,
) {
    let (_, e) = fetch_ptrs(
        storage,
        vec![],
        vec![inputs[0][0], inputs[0][1], inputs[1][0], inputs[1][1]],
    );
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::lookup_pair([e[0], e[1], e[2], e[3]], [d[0], d[1]], trace_len, worker)
    });
}

/// LookupPairFromMaterializedBaseInputs
pub fn lookup_base_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    worker: &Worker,
) {
    let (b, _) = fetch_ptrs(storage, inputs.to_vec(), vec![]);
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::lookup_base_pair([b[0], b[1]], [d[0], d[1]], g, trace_len, worker)
    });
}

/// LookupPairFromMaterializedVectorInputs
pub fn lookup_ext_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    worker: &Worker,
) {
    let (_, e) = fetch_ptrs(storage, vec![], inputs.to_vec());
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::lookup_ext_pair([e[0], e[1]], [d[0], d[1]], g, trace_len, worker)
    });
}

/// LookupUnbalancedPairWithMaterializedBaseInputs
pub fn lookup_unbalanced_base<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [GKRAddress; 2],
    remainder: GKRAddress,
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    worker: &Worker,
) {
    let (b, e) = fetch_ptrs(storage, vec![remainder], inputs.to_vec());
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::unbalanced_base(b[0], [e[0], e[1]], [d[0], d[1]], g, trace_len, worker)
    });
}

/// LookupUnbalancedPairWithMaterializedVectorInputs
pub fn lookup_unbalanced_ext<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [GKRAddress; 2],
    remainder: GKRAddress,
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    worker: &Worker,
) {
    let (_, e) = fetch_ptrs(storage, vec![], vec![inputs[0], inputs[1], remainder]);
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::unbalanced_ext([e[0], e[1], e[2]], [d[0], d[1]], g, trace_len, worker)
    });
}

/// LookupFromMaterializedBaseInputWithSetup
pub fn lookup_base_minus_multiplicity<F: PrimeField, E: FieldExtension<F> + Field>(
    input: GKRAddress,
    setup: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    worker: &Worker,
) {
    let (b, _) = fetch_ptrs(storage, vec![input, setup[0], setup[1]], vec![]);
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::base_minus_mult([b[0], b[1], b[2]], [d[0], d[1]], g, trace_len, worker)
    });
}

/// LookupFromMaterializedVectorInputWithSetup
pub fn lookup_ext_minus_multiplicity<F: PrimeField, E: FieldExtension<F> + Field>(
    input: GKRAddress,
    setup: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    worker: &Worker,
) {
    let (b, e) = fetch_ptrs(storage, vec![setup[0]], vec![input, setup[1]]);
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::ext_minus_mult(b[0], [e[0], e[1]], [d[0], d[1]], g, trace_len, worker)
    });
}

/// LookupWithCachedDensAndSetup
pub fn masked_lookup_with_setup<F: PrimeField, E: FieldExtension<F> + Field>(
    input: [GKRAddress; 2],
    setup: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    worker: &Worker,
) {
    let (b, e) = fetch_ptrs(storage, vec![input[0], setup[0]], vec![input[1], setup[1]]);
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::masked_lookup_setup([b[0], b[1]], [e[0], e[1]], [d[0], d[1]], g, trace_len, worker)
    });
}

/// MaskIntoIdentityProduct
pub fn mask_into_identity<F: PrimeField, E: FieldExtension<F> + Field>(
    input: GKRAddress,
    mask: GKRAddress,
    output: GKRAddress,
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    worker: &Worker,
) {
    let (b, e) = fetch_ptrs(storage, vec![mask], vec![input]);
    with_outputs(storage, &[output], expected_output_layer, trace_len, |d| {
        core_ops::mask_identity(b[0], e[0], d[0], trace_len, worker)
    });
}

/// TrivialProduct / InitialGrandProductFromCaches
pub fn pairwise_product<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [GKRAddress; 2],
    output: GKRAddress,
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    worker: &Worker,
) {
    let (_, e) = fetch_ptrs(storage, vec![], inputs.to_vec());
    with_outputs(storage, &[output], expected_output_layer, trace_len, |d| {
        core_ops::pairwise([e[0], e[1]], d[0], trace_len, worker)
    });
}

/// Cache::MemoryTuple / MaterializeGrandProductTermExpression, or `None`
/// when the relation is not compilable (the caller runs the scalar path).
pub fn materialize_memory_tuple<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &SpecialMemoryContributionRelation,
    storage: &GKRStorage<F, E>,
    trace_len: usize,
    external_challenges: &GKRExternalChallenges<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    worker: &Worker,
) -> Option<Box<[E]>> {
    let cols = mem_col_ptrs(storage, compiled_circuit);
    let plan = compile_mem_query(rel, challenges_bb(external_challenges), &cols)?;
    Some(make_ext(storage, trace_len, |dst| {
        run_blocks(trace_len, worker, |r| unsafe { plan_block(&plan, dst, r) })
    }))
}

/// InitialGrandProductWithoutCaches: `false` when a query is not compilable.
pub fn product_without_caches<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: &[SpecialMemoryContributionRelation; 2],
    output: GKRAddress,
    storage: &mut GKRStorage<F, E>,
    external_challenges: &GKRExternalChallenges<F, E>,
    expected_output_layer: usize,
    compiled_circuit: &GKRCircuitArtifact<F>,
    trace_len: usize,
    worker: &Worker,
) -> bool {
    let cols = mem_col_ptrs(storage, compiled_circuit);
    let ch = challenges_bb(external_challenges);
    let (Some(pl), Some(pr)) = (
        compile_mem_query(&inputs[0], ch, &cols),
        compile_mem_query(&inputs[1], ch, &cols),
    ) else {
        return false;
    };
    let values = make_ext(storage, trace_len, |dst| {
        run_blocks(trace_len, worker, |r| unsafe { plan_product_block(&pl, &pr, dst, r) })
    });
    output.assert_as_layer(expected_output_layer);
    storage.insert_extension_at_layer(expected_output_layer, output, ExtensionFieldPoly::new(values));
    true
}

/// InitsOrTeardownsInitialPair
pub fn inits_and_teardowns_pair<F: PrimeField, E: FieldExtension<F> + Field, const WORD_BITS: u32>(
    ts_and_value: &InitsOrTeardownsTimestampAndValue,
    address_high_bits: [u32; 2],
    storage: &GKRStorage<F, E>,
    trace_len: usize,
    external_challenges: &GKRExternalChallenges<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    worker: &Worker,
) -> Box<[E]> {
    let high_bits_offset =
        crate::gkr::high_bits_offset_for_inits_and_teardowns::<WORD_BITS>(trace_len);
    let cols = mem_col_ptrs(storage, compiled_circuit);
    let ch = challenges_bb(external_challenges);
    let low = base_ptr(storage.get_base_layer(GKRAddress::VirtualSetup(
        VirtualSetupPoly::InitsAndTeardownsLow,
    )));
    let high = base_ptr(storage.get_base_layer(GKRAddress::VirtualSetup(
        VirtualSetupPoly::InitsAndTeardownsHigh,
    )));
    let sides: [Option<([usize; 2], [usize; 2])>; 2] = match ts_and_value {
        InitsOrTeardownsTimestampAndValue::Init => [None, None],
        InitsOrTeardownsTimestampAndValue::Teardown {
            lhs_timestamp,
            lhs_value,
            rhs_timestamp,
            rhs_value,
        } => [
            Some((*lhs_timestamp, *lhs_value)),
            Some((*rhs_timestamp, *rhs_value)),
        ],
    };
    let pl = compile_init_or_teardown(ch, address_high_bits[0], high_bits_offset, sides[0], &cols, low, high);
    let pr = compile_init_or_teardown(ch, address_high_bits[1], high_bits_offset, sides[1], &cols, low, high);
    make_ext(storage, trace_len, |dst| {
        run_blocks(trace_len, worker, |r| unsafe { plan_product_block(&pl, &pr, dst, r) })
    })
}

/// Cache::SingleColumnLookup / MaterializeSingleLookupInput: the Montgomery
/// form of the witness range-check mapping as a (pooled) base poly.
pub fn single_column_lookup_cache<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    output: GKRAddress,
    relation: &SingleColumnLookupRelation<F>,
    range_check_width: u32,
    storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    worker: &Worker,
) {
    let mut dst = storage.alloc_base_uninit(trace_len);
    let dp = dst.as_mut_ptr() as usize;
    check_out_alignment(dp);
    if range_check_width == 16 {
        let source = core::mem::replace(
            &mut witness_trace.range_check_16_lookup_mapping[relation.lookup_set_index],
            vec![],
        );
        assert_eq!(source.len(), trace_len);
        core_ops::single_column::<true>(source.as_ptr() as usize, dp, trace_len, worker);
    } else if range_check_width == common_constants::TIMESTAMP_COLUMNS_NUM_BITS {
        let source = core::mem::replace(
            &mut witness_trace.timestamp_range_check_lookup_mapping[relation.lookup_set_index],
            vec![],
        );
        assert_eq!(source.len(), trace_len);
        core_ops::single_column::<false>(source.as_ptr() as usize, dp, trace_len, worker);
    } else {
        unreachable!(
            "unknown single column lookup range check of width {}",
            range_check_width
        );
    }
    output.assert_as_layer(layer_idx);
    storage.insert_base_field_at_layer(
        layer_idx,
        output,
        BaseFieldPoly::new(unsafe { dst.assume_init() }),
    );
}

/// LookupPairFromBaseInputs (range check 16 / timestamp range check)
pub fn range_check_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: &[SingleColumnLookupRelation<F>; 2],
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    range_check_width: u32,
    worker: &Worker,
) {
    let g = limbs(&gamma);
    let [lhs, rhs] = inputs;
    if range_check_width == 16 {
        let l = core::mem::replace(
            &mut witness_trace.range_check_16_lookup_mapping[lhs.lookup_set_index],
            vec![],
        );
        let r = core::mem::replace(
            &mut witness_trace.range_check_16_lookup_mapping[rhs.lookup_set_index],
            vec![],
        );
        assert_eq!(l.len(), trace_len);
        assert_eq!(r.len(), trace_len);
        let maps = [l.as_ptr() as usize, r.as_ptr() as usize];
        with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
            core_ops::range_check_pair::<true>(maps, [d[0], d[1]], g, trace_len, worker)
        });
    } else {
        assert_eq!(range_check_width, common_constants::TIMESTAMP_COLUMNS_NUM_BITS);
        let l = core::mem::replace(
            &mut witness_trace.timestamp_range_check_lookup_mapping[lhs.lookup_set_index],
            vec![],
        );
        let r = core::mem::replace(
            &mut witness_trace.timestamp_range_check_lookup_mapping[rhs.lookup_set_index],
            vec![],
        );
        assert_eq!(l.len(), trace_len);
        assert_eq!(r.len(), trace_len);
        let maps = [l.as_ptr() as usize, r.as_ptr() as usize];
        with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
            core_ops::range_check_pair::<false>(maps, [d[0], d[1]], g, trace_len, worker)
        });
    }
}

/// Cache::VectorizedLookup: `table[mapping[row]]`, decoder rows masked to
/// the fill value.
pub fn vector_lookup_input<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &VectorLookupRelation<F>,
    storage: &GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    decoder_lookup_fill_value: E,
    decoder_predicate_address: GKRAddress,
    worker: &Worker,
) -> Box<[E]> {
    let lookup_set_index = rel.lookup_set_index;
    let is_decoder_lookup = lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX;
    let mapping = if is_decoder_lookup == false {
        &witness_trace.generic_lookup_mapping[lookup_set_index]
    } else {
        assert!(witness_trace.generic_lookup_mapping.len() > 0);
        witness_trace.generic_lookup_mapping.last().unwrap()
    };
    assert_eq!(mapping.len(), trace_len);
    let pred = if is_decoder_lookup {
        Some((
            base_ptr(storage.get_base_layer(decoder_predicate_address)),
            limbs(&decoder_lookup_fill_value),
        ))
    } else {
        None
    };
    let (table, map) = (ext_ptr(preprocessed_generic_lookup), mapping.as_ptr() as usize);
    make_ext(storage, trace_len, |dst| {
        core_ops::vector_lookup(table, map, pred, dst, trace_len, worker)
    })
}

/// LookupWithDensAndSetupExpressions (decoder)
pub fn decoder_lookup_minus_setup<F: PrimeField, E: FieldExtension<F> + Field>(
    decoder_predicate_address: GKRAddress,
    decoder_relation: &VectorLookupRelation<F>,
    multiplicity_address: GKRAddress,
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    gamma: E,
    decoder_lookup_fill_value: E,
    worker: &Worker,
) {
    assert_eq!(decoder_relation.lookup_set_index, DECODER_LOOKUP_FORMAL_SET_INDEX);
    let mapping = {
        assert!(witness_trace.generic_lookup_mapping.len() > 0);
        witness_trace.generic_lookup_mapping.pop().unwrap()
    };
    assert_eq!(mapping.len(), trace_len);
    let pred = base_ptr(storage.get_base_layer(decoder_predicate_address));
    let mult = base_ptr(storage.get_base_layer(multiplicity_address));
    let table = (ext_ptr(preprocessed_generic_lookup), preprocessed_generic_lookup.len());
    let (g, fill) = (limbs(&gamma), limbs(&decoder_lookup_fill_value));
    let map = mapping.as_ptr() as usize;
    with_outputs(storage, &outputs, 1, trace_len, |d| {
        core_ops::decoder_minus_setup(table, map, pred, mult, fill, g, [d[0], d[1]], trace_len, worker)
    });
}

/// LookupPairFromVectorInputs
pub fn lookup_expressions_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: &[VectorLookupRelation<F>; 2],
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    expected_output_layer: usize,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    gamma: E,
    worker: &Worker,
) {
    assert_ne!(inputs[0].lookup_set_index, DECODER_LOOKUP_FORMAL_SET_INDEX);
    assert_ne!(inputs[1].lookup_set_index, DECODER_LOOKUP_FORMAL_SET_INDEX);
    let l = core::mem::replace(
        &mut witness_trace.generic_lookup_mapping[inputs[0].lookup_set_index],
        Vec::new(),
    );
    let r = core::mem::replace(
        &mut witness_trace.generic_lookup_mapping[inputs[1].lookup_set_index],
        Vec::new(),
    );
    assert_eq!(l.len(), trace_len);
    assert_eq!(r.len(), trace_len);
    let table = ext_ptr(preprocessed_generic_lookup);
    let maps = [l.as_ptr() as usize, r.as_ptr() as usize];
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::expressions_pair(table, maps, g, [d[0], d[1]], trace_len, worker)
    });
}

/// LookupUnbalancedPairWithVectorInputs
pub fn lookup_expressions_pair_with_remainder<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [GKRAddress; 2],
    remainder: &VectorLookupRelation<F>,
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    expected_output_layer: usize,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    gamma: E,
    worker: &Worker,
) {
    assert_ne!(remainder.lookup_set_index, DECODER_LOOKUP_FORMAL_SET_INDEX);
    let mapping = core::mem::replace(
        &mut witness_trace.generic_lookup_mapping[remainder.lookup_set_index],
        Vec::new(),
    );
    assert_eq!(mapping.len(), trace_len);
    let ab = [
        ext_ptr(storage.get_ext_poly(inputs[0])),
        ext_ptr(storage.get_ext_poly(inputs[1])),
    ];
    let table = ext_ptr(preprocessed_generic_lookup);
    let map = mapping.as_ptr() as usize;
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, expected_output_layer, trace_len, |d| {
        core_ops::expressions_pair_with_remainder(table, map, ab, g, [d[0], d[1]], trace_len, worker)
    });
}

/// LookupFromVectorInputWithSetup
pub fn lookup_expression_minus_setup<F: PrimeField, E: FieldExtension<F> + Field>(
    input: &VectorLookupRelation<F>,
    multiplicity_address: GKRAddress,
    outputs: [GKRAddress; 2],
    storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    gamma: E,
    worker: &Worker,
) {
    assert_ne!(input.lookup_set_index, DECODER_LOOKUP_FORMAL_SET_INDEX);
    let mapping = core::mem::replace(
        &mut witness_trace.generic_lookup_mapping[input.lookup_set_index],
        Vec::new(),
    );
    assert_eq!(mapping.len(), trace_len);
    let mult = base_ptr(storage.get_base_layer(multiplicity_address));
    let table = (ext_ptr(preprocessed_generic_lookup), preprocessed_generic_lookup.len());
    let map = mapping.as_ptr() as usize;
    let g = limbs(&gamma);
    with_outputs(storage, &outputs, 1, trace_len, |d| {
        core_ops::expression_minus_setup(table, map, mult, g, [d[0], d[1]], trace_len, worker)
    });
}

// ---------------------------------------------------------------------------
// parity tests against scalar references of the same formulas
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn pseudo_base(seed: &mut u64) -> BF {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        BF::from_u32_with_reduction((*seed >> 33) as u32)
    }
    fn pseudo_ext(seed: &mut u64) -> BE {
        BE::from_array_of_base(core::array::from_fn(|_| pseudo_base(seed)))
    }
    fn ext_vec(n: usize, seed: &mut u64) -> Vec<BE> {
        (0..n).map(|_| pseudo_ext(seed)).collect()
    }
    fn base_vec(n: usize, seed: &mut u64) -> Vec<BF> {
        (0..n).map(|_| pseudo_base(seed)).collect()
    }
    fn bool_vec(n: usize, seed: &mut u64) -> Vec<BF> {
        (0..n)
            .map(|_| {
                if pseudo_base(seed).raw_u32_value() & 1 == 1 {
                    BF::ONE
                } else {
                    BF::ZERO
                }
            })
            .collect()
    }
    fn idx_vec(n: usize, bound: u32, seed: &mut u64) -> Vec<u32> {
        (0..n)
            .map(|_| pseudo_base(seed).raw_u32_value() % bound)
            .collect()
    }
    fn out(n: usize) -> Box<[MaybeUninit<BE>]> {
        Box::new_uninit_slice(n)
    }
    fn p<T>(s: &[T]) -> usize {
        s.as_ptr() as usize
    }
    fn pm<T>(s: &mut [T]) -> usize {
        s.as_mut_ptr() as usize
    }
    fn done(b: Box<[MaybeUninit<BE>]>) -> Vec<BE> {
        unsafe { b.assume_init() }.into_vec()
    }
    fn add(a: BE, b: BE) -> BE {
        let mut r = a;
        r.add_assign(&b);
        r
    }
    fn sub(a: BE, b: BE) -> BE {
        let mut r = a;
        r.sub_assign(&b);
        r
    }
    fn mul(a: BE, b: BE) -> BE {
        let mut r = a;
        r.mul_assign(&b);
        r
    }
    fn mulb(a: BE, b: BF) -> BE {
        let mut r = a;
        r.mul_assign_by_base(&b);
        r
    }
    fn addb(a: BE, b: BF) -> BE {
        let mut r = a;
        r.add_assign_base(&b);
        r
    }

    #[test]
    fn avx512_forward_relations_match_scalar() {
        if !is_x86_feature_detected!("avx512f") {
            eprintln!("avx512f not available: skipping");
            return;
        }
        let w = Worker::new_with_num_threads(3);
        let mut seed = 77u64;
        let n = 1usize << 12;
        let g = pseudo_ext(&mut seed);
        let gl = limbs(&g);
        let (a, b, c, d) = (
            ext_vec(n, &mut seed),
            ext_vec(n, &mut seed),
            ext_vec(n, &mut seed),
            ext_vec(n, &mut seed),
        );
        let (x, y, z) = (base_vec(n, &mut seed), base_vec(n, &mut seed), base_vec(n, &mut seed));
        let mask = bool_vec(n, &mut seed);

        // lookup pair: a d + c b, b d
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::lookup_pair([p(&a), p(&b), p(&c), p(&d)], [pm(&mut o0), pm(&mut o1)], n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            assert_eq!(o0[i], add(mul(a[i], d[i]), mul(c[i], b[i])), "lookup pair num {i}");
            assert_eq!(o1[i], mul(b[i], d[i]), "lookup pair den {i}");
        }
        // lookup base pair: (x+g) + (y+g), (x+g)(y+g)
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::lookup_base_pair([p(&x), p(&y)], [pm(&mut o0), pm(&mut o1)], gl, n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let (bb, dd) = (addb(g, x[i]), addb(g, y[i]));
            assert_eq!(o0[i], add(bb, dd), "base pair num {i}");
            assert_eq!(o1[i], mul(bb, dd), "base pair den {i}");
        }
        // lookup ext pair: (a+g) + (b+g), (a+g)(b+g)
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::lookup_ext_pair([p(&a), p(&b)], [pm(&mut o0), pm(&mut o1)], gl, n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let (bb, dd) = (add(a[i], g), add(b[i], g));
            assert_eq!(o0[i], add(bb, dd), "ext pair num {i}");
            assert_eq!(o1[i], mul(bb, dd), "ext pair den {i}");
        }
        // unbalanced base: a (x+g) + b, b (x+g)
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::unbalanced_base(p(&x), [p(&a), p(&b)], [pm(&mut o0), pm(&mut o1)], gl, n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let dd = addb(g, x[i]);
            assert_eq!(o0[i], add(mul(a[i], dd), b[i]), "unbalanced base num {i}");
            assert_eq!(o1[i], mul(b[i], dd), "unbalanced base den {i}");
        }
        // unbalanced ext: a (d+g) + b, b (d+g)
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::unbalanced_ext([p(&a), p(&b), p(&d)], [pm(&mut o0), pm(&mut o1)], gl, n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let dd = add(d[i], g);
            assert_eq!(o0[i], add(mul(a[i], dd), b[i]), "unbalanced ext num {i}");
            assert_eq!(o1[i], mul(b[i], dd), "unbalanced ext den {i}");
        }
        // base minus mult: (z+g) - y (x+g), (x+g)(z+g)
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::base_minus_mult([p(&x), p(&y), p(&z)], [pm(&mut o0), pm(&mut o1)], gl, n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let (bb, dd) = (addb(g, x[i]), addb(g, z[i]));
            assert_eq!(o0[i], sub(dd, mulb(bb, y[i])), "base minus mult num {i}");
            assert_eq!(o1[i], mul(bb, dd), "base minus mult den {i}");
        }
        // ext minus mult: (b+g) - x (a+g), (a+g)(b+g)
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::ext_minus_mult(p(&x), [p(&a), p(&b)], [pm(&mut o0), pm(&mut o1)], gl, n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let (bb, dd) = (add(a[i], g), add(b[i], g));
            assert_eq!(o0[i], sub(dd, mulb(bb, x[i])), "ext minus mult num {i}");
            assert_eq!(o1[i], mul(bb, dd), "ext minus mult den {i}");
        }
        // masked lookup with setup: x (b+g) - y (a+g), (a+g)(b+g)
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::masked_lookup_setup([p(&x), p(&y)], [p(&a), p(&b)], [pm(&mut o0), pm(&mut o1)], gl, n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let (bb, dd) = (add(a[i], g), add(b[i], g));
            assert_eq!(o0[i], sub(mulb(dd, x[i]), mulb(bb, y[i])), "masked setup num {i}");
            assert_eq!(o1[i], mul(bb, dd), "masked setup den {i}");
        }
        // mask into identity: (a - 1) mask + 1
        let mut o0 = out(n);
        core_ops::mask_identity(p(&mask), p(&a), pm(&mut o0), n, &w);
        let o0 = done(o0);
        for i in 0..n {
            let mut v = a[i];
            v.sub_assign_base(&BF::ONE);
            v.mul_assign_by_base(&mask[i]);
            v.add_assign_base(&BF::ONE);
            assert_eq!(o0[i], v, "mask identity {i}");
        }
        // pairwise: a b
        let mut o0 = out(n);
        core_ops::pairwise([p(&a), p(&b)], pm(&mut o0), n, &w);
        let o0 = done(o0);
        for i in 0..n {
            assert_eq!(o0[i], mul(a[i], b[i]), "pairwise {i}");
        }
    }

    #[test]
    fn avx512_forward_mappings_match_scalar() {
        if !is_x86_feature_detected!("avx512f") {
            eprintln!("avx512f not available: skipping");
            return;
        }
        let w = Worker::new_with_num_threads(3);
        let mut seed = 91u64;
        let n = 1usize << 12;
        let g = pseudo_ext(&mut seed);
        let gl = limbs(&g);
        let fill = pseudo_ext(&mut seed);
        let fl = limbs(&fill);
        // a table shorter than the trace and not a multiple of 16
        let table_len = n / 2 + 5;
        let table = ext_vec(table_len, &mut seed);
        let m1 = idx_vec(n, table_len as u32, &mut seed);
        let m2 = idx_vec(n, table_len as u32, &mut seed);
        let m16: Vec<u16> = (0..n).map(|_| (pseudo_base(&mut seed).raw_u32_value() & 0xffff) as u16).collect();
        let m19: Vec<u32> = (0..n).map(|_| pseudo_base(&mut seed).raw_u32_value() & ((1 << 19) - 1)).collect();
        let pred = bool_vec(n, &mut seed);
        let mult = base_vec(n, &mut seed);
        let (a, b) = (ext_vec(n, &mut seed), ext_vec(n, &mut seed));
        let setup = |row: usize| table.get(row).copied().unwrap_or(BE::ZERO);
        let tbl = (p(&table), table_len);

        // single column caches (u16 and u32 mappings)
        for u16_case in [true, false] {
            let mut o: Box<[MaybeUninit<BF>]> = Box::new_uninit_slice(n);
            if u16_case {
                core_ops::single_column::<true>(p(&m16), pm(&mut o), n, &w);
            } else {
                core_ops::single_column::<false>(p(&m19), pm(&mut o), n, &w);
            }
            let o = unsafe { o.assume_init() };
            for i in 0..n {
                let v = if u16_case { m16[i] as u32 } else { m19[i] };
                assert_eq!(o[i], BF::from_u32_unchecked(v), "single column {u16_case} {i}");
            }
        }
        // range check pairs
        for u16_case in [true, false] {
            let (mut o0, mut o1) = (out(n), out(n));
            if u16_case {
                core_ops::range_check_pair::<true>([p(&m16), p(&m16[8..])], [pm(&mut o0), pm(&mut o1)], gl, n - 16, &w);
            } else {
                core_ops::range_check_pair::<false>([p(&m19), p(&m19[8..])], [pm(&mut o0), pm(&mut o1)], gl, n - 16, &w);
            }
            let (o0, o1) = (done(o0), done(o1));
            for i in 0..n - 16 {
                let (v1, v2) = if u16_case {
                    (m16[i] as u32, m16[i + 8] as u32)
                } else {
                    (m19[i], m19[i + 8])
                };
                let lhs = addb(g, BF::from_u32_unchecked(v1));
                let rhs = addb(g, BF::from_u32_unchecked(v2));
                assert_eq!(o0[i], add(lhs, rhs), "range pair num {u16_case} {i}");
                assert_eq!(o1[i], mul(lhs, rhs), "range pair den {u16_case} {i}");
            }
        }
        // vector lookup (plain and decoder-masked)
        let mut o0 = out(n);
        core_ops::vector_lookup(p(&table), p(&m1), None, pm(&mut o0), n, &w);
        let o0 = done(o0);
        for i in 0..n {
            assert_eq!(o0[i], table[m1[i] as usize], "vector lookup {i}");
        }
        let mut o0 = out(n);
        core_ops::vector_lookup(p(&table), p(&m1), Some((p(&pred), fl)), pm(&mut o0), n, &w);
        let o0 = done(o0);
        for i in 0..n {
            let e = if pred[i].as_boolean() { table[m1[i] as usize] } else { fill };
            assert_eq!(o0[i], e, "masked vector lookup {i}");
        }
        // decoder minus setup
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::decoder_minus_setup(tbl, p(&m1), p(&pred), p(&mult), fl, gl, [pm(&mut o0), pm(&mut o1)], n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let looked = if pred[i].as_boolean() { table[m1[i] as usize] } else { fill };
            let bb = add(looked, g);
            let dd = add(setup(i), g);
            assert_eq!(o0[i], sub(mulb(dd, pred[i]), mulb(bb, mult[i])), "decoder num {i}");
            assert_eq!(o1[i], mul(bb, dd), "decoder den {i}");
        }
        // expressions pair
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::expressions_pair(p(&table), [p(&m1), p(&m2)], gl, [pm(&mut o0), pm(&mut o1)], n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let (bb, dd) = (add(table[m1[i] as usize], g), add(table[m2[i] as usize], g));
            assert_eq!(o0[i], add(dd, bb), "expressions pair num {i}");
            assert_eq!(o1[i], mul(bb, dd), "expressions pair den {i}");
        }
        // expressions pair with remainder
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::expressions_pair_with_remainder(p(&table), p(&m2), [p(&a), p(&b)], gl, [pm(&mut o0), pm(&mut o1)], n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let dd = add(table[m2[i] as usize], g);
            assert_eq!(o0[i], add(mul(dd, a[i]), b[i]), "remainder num {i}");
            assert_eq!(o1[i], mul(b[i], dd), "remainder den {i}");
        }
        // expression minus setup
        let (mut o0, mut o1) = (out(n), out(n));
        core_ops::expression_minus_setup(tbl, p(&m1), p(&mult), gl, [pm(&mut o0), pm(&mut o1)], n, &w);
        let (o0, o1) = (done(o0), done(o1));
        for i in 0..n {
            let bb = add(table[m1[i] as usize], g);
            let dd = add(setup(i), g);
            assert_eq!(o0[i], sub(dd, mulb(bb, mult[i])), "minus setup num {i}");
            assert_eq!(o1[i], mul(bb, dd), "minus setup den {i}");
        }
    }

    #[test]
    fn avx512_forward_plans_match_scalar() {
        if !is_x86_feature_detected!("avx512f") {
            eprintln!("avx512f not available: skipping");
            return;
        }
        let w = Worker::new_with_num_threads(3);
        let mut seed = 5u64;
        let n = 1usize << 12;
        let cols: Vec<Vec<BF>> = (0..6).map(|_| base_vec(n, &mut seed)).collect();
        let col_ptrs: Vec<usize> = cols.iter().map(|c| p(c)).collect();
        let ch: Vec<BE> = (0..6).map(|_| pseudo_ext(&mut seed)).collect();
        let additive = pseudo_ext(&mut seed);
        let one = one_raw();
        let two = BF::from_u32_unchecked(2);
        let k7 = BF::from_u32_unchecked(7);
        let mut plan = Plan::new(&additive);
        // limb-0 term: 1 - col0
        plan.terms.push(Term {
            ch: None,
            cols: vec![(BF::MINUS_ONE.raw_u32_value(), col_ptrs[0])],
            constant: one,
        });
        plan.linear(&ch[0], vec![(one, col_ptrs[1])], k7.raw_u32_value());
        plan.linear(&ch[1], vec![(one, col_ptrs[2]), (two.raw_u32_value(), col_ptrs[3])], 0);
        plan.linear(&ch[2], vec![(k7.raw_u32_value(), col_ptrs[4])], 0);
        let mut plan_r = Plan::new(&ch[3]);
        plan_r.linear(&ch[4], vec![(one, col_ptrs[5])], one);
        let scalar = |row: usize| -> BE {
            let mut r = additive;
            let mut t0 = BF::ONE;
            t0.sub_assign(&cols[0][row]);
            r.add_assign_base(&t0);
            let mut t1 = cols[1][row];
            t1.add_assign(&k7);
            r.add_assign(&mulb(ch[0], t1));
            let mut t2 = cols[3][row];
            t2.mul_assign(&two);
            t2.add_assign(&cols[2][row]);
            r.add_assign(&mulb(ch[1], t2));
            let mut t3 = cols[4][row];
            t3.mul_assign(&k7);
            r.add_assign(&mulb(ch[2], t3));
            r
        };
        let scalar_r = |row: usize| -> BE {
            let mut t = cols[5][row];
            t.add_assign(&BF::ONE);
            add(ch[3], mulb(ch[4], t))
        };
        let mut o0 = out(n);
        let dp = pm(&mut o0);
        run_blocks(n, &w, |r| unsafe { plan_block(&plan, dp, r) });
        let o0 = done(o0);
        let mut o1 = out(n);
        let dp = pm(&mut o1);
        run_blocks(n, &w, |r| unsafe { plan_product_block(&plan, &plan_r, dp, r) });
        let o1 = done(o1);
        for i in 0..n {
            assert_eq!(o0[i], scalar(i), "plan {i}");
            assert_eq!(o1[i], mul(scalar(i), scalar_r(i)), "plan product {i}");
        }
    }
}
