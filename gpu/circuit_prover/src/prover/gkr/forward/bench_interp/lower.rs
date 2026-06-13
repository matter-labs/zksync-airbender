//! CPU→GPU lowering of a `gkr_eval_isa` compiled forward program into the
//! `interp_desc` ABI (`native/bench/gkr_fwd_interp.cu`). Test/bench-only code
//! (the module is `cfg(all(test, feature = "bench"))`), so `gkr_eval_isa` is
//! a dev-dependency and upstream-import rules don't apply.

use cs::definitions::gkr::RamWordRepresentation;
use cs::gkr_compiler::codegen_ir::{
    CacheKind, Domain, ExprNode, GateKind, LinearComb, MemTupleDescriptor,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict as AddrSpace, CompiledAddressStrict as Addr,
    CompiledMemoryTimestamp as Ts,
};
use gkr_eval_isa::compiler::fwd::{CompiledForward, PayloadRecord};
use gkr_eval_isa::isa::{encode, Dst, Program};

use crate::primitives::field::{BF, E4};
use field::{Field, FieldExtension, PrimeField};

/// Host-side image of the kernel's `interp_desc` payload. The caller uploads
/// `lanes`, `source_ptrs`, `output_ptrs`, `output_e4` and `consts` to device
/// buffers and assembles an `InterpDesc` from them.
pub(crate) struct LoweredProgram {
    /// `gkr_eval_isa::isa::encode(&cf.program)` verbatim.
    pub lanes: Vec<u16>,
    pub n_instr: u32,
    /// ONE pointer table matching the kernel ABI: bf source columns at
    /// `[0, n_sources_bf)` followed by e4 source columns. The encoded
    /// `Operand::Source { id, e4 }` banks are separate id spaces
    /// (interp.rs `read`); the kernel indexes e4 ids at `n_sources_bf + id`.
    pub source_ptrs: Vec<*const u8>,
    pub n_sources_bf: u32,
    /// Per ORIGINAL output slot j (len = `program.n_outputs`); null for slots
    /// the program never writes (native-stored outputs).
    pub output_ptrs: Vec<*mut u8>,
    /// Bitset over output slots: 1 = the slot buffer holds e4 elements.
    pub output_e4: Vec<u32>,
    /// Constant table converted to device-ready Montgomery form. The CPU
    /// interpreter stores canonical u32 and converts on read
    /// (`Bf::from_u32_with_reduction`, interp.rs); the kernel reads raw bf.
    pub consts: Vec<BF>,
    /// Cell-file size = `program.n_slot_cells` (the compiler's address-based
    /// high water; every encoded cell index is below it).
    pub budget_cells: u32,
}

/// Per-output-slot write width from the program's own `Dst::Output`
/// instructions (mirrors the CPU write path: interp.rs stores whatever
/// `e4_result` says, so the GPU buffer width must match it).
/// `None` = slot never written.
pub(crate) fn output_widths(p: &Program) -> Vec<Option<bool>> {
    let mut widths = vec![None::<bool>; p.n_outputs as usize];
    for ins in &p.instrs {
        if let Dst::Output(j) = ins.dst {
            let w = &mut widths[j as usize];
            assert!(
                w.is_none() || *w == Some(ins.e4_result),
                "output slot {j} written with two widths"
            );
            *w = Some(ins.e4_result);
        }
    }
    widths
}

/// Lower a compiled forward program to the kernel ABI.
///
/// Resolver contract:
/// - `resolve_src_bf(i)` / `resolve_src_e4(i)` take the SOURCE-BANK INDEX
///   (the operand-lane id, i.e. an index into `cf.source_map.bf` /
///   `cf.source_map.e4`) — NOT the arena node id. Callers needing the node
///   can map via `cf.source_map.bf[i]` / `cf.source_map.e4[i]`. They return
///   the device column base pointer (element stride 4B bf / 16B e4).
/// - `resolve_out(j)` takes the ORIGINAL output slot index (the `j` of
///   `cf.outputs`) and returns the device column base + whether the column
///   holds e4 elements; the width is cross-checked against the program.
pub(crate) fn lower_program(
    cf: &CompiledForward,
    resolve_src_bf: impl Fn(usize) -> *const u8,
    resolve_src_e4: impl Fn(usize) -> *const u8,
    resolve_out: impl Fn(u16) -> (*mut u8, bool),
) -> LoweredProgram {
    let p = &cf.program;
    assert_eq!(
        p.n_fixed_cells, 0,
        "forward programs have no fixed-reg file"
    );
    assert_eq!(p.n_gate_ins, 0, "forward programs have no gate-in staging");
    // The kernel writes a zero sentinel for ANY NativeK with a Slot dst (it
    // has no payload table until Task 4); the CPU writes sentinels only for
    // cache payloads. Pin the equivalence here so a non-cache Slot-dst
    // NativeK cannot silently diverge.
    for ins in &p.instrs {
        if ins.op == gkr_eval_isa::isa::Op::NativeK {
            let is_cache = p.payloads[ins.payload.unwrap() as usize].cache.is_some();
            let has_slot_dst = matches!(ins.dst, Dst::Slot(_));
            assert_eq!(
                is_cache, has_slot_dst,
                "NativeK Slot-dst <=> cache payload violated"
            );
        }
    }
    let lanes = encode(p);

    let n_bf = p.n_sources_bf as usize;
    let n_e4 = p.n_sources_e4 as usize;
    assert_eq!(cf.source_map.bf.len(), n_bf);
    assert_eq!(cf.source_map.e4.len(), n_e4);
    let mut source_ptrs = Vec::with_capacity(n_bf + n_e4);
    source_ptrs.extend((0..n_bf).map(&resolve_src_bf));
    source_ptrs.extend((0..n_e4).map(&resolve_src_e4));

    let widths = output_widths(p);
    // Every slot the program writes must be in cf.outputs (so the test can
    // hand it a buffer), and vice versa every cf.outputs entry is written.
    let n_out = p.n_outputs as usize;
    let mut output_ptrs: Vec<*mut u8> = vec![std::ptr::null_mut(); n_out];
    let mut output_e4 = vec![0u32; n_out.div_ceil(32).max(1)];
    for &(j, _node) in &cf.outputs {
        let e4 = widths[j as usize]
            .unwrap_or_else(|| panic!("cf.outputs slot {j} never written by the program"));
        let (ptr, slot_e4) = resolve_out(j);
        assert!(
            !ptr.is_null(),
            "resolver returned null for written output slot {j}"
        );
        assert_eq!(
            slot_e4, e4,
            "output slot {j}: resolver width disagrees with the program"
        );
        output_ptrs[j as usize] = ptr;
        if e4 {
            output_e4[j as usize / 32] |= 1 << (j as usize % 32);
        }
    }
    for (j, w) in widths.iter().enumerate() {
        if w.is_some() {
            assert!(
                cf.outputs.iter().any(|&(jj, _)| jj as usize == j),
                "program writes output slot {j} absent from cf.outputs"
            );
        }
    }

    let consts: Vec<BF> = p
        .consts
        .iter()
        .map(|&c| BF::from_u32_with_reduction(c))
        .collect();

    LoweredProgram {
        lanes,
        n_instr: p.instrs.len() as u32,
        source_ptrs,
        n_sources_bf: p.n_sources_bf as u32,
        output_ptrs,
        output_e4,
        consts,
        budget_cells: p.n_slot_cells as u32,
    }
}

// ===========================================================================
// Task 4: NativeK payload lowering.
//
// Variable-size tagged records in ONE byte buffer + a u32 offset per payload
// index. The device reader (`fire_payload`, native/bench/gkr_fwd_interp.cu)
// carries the authoritative ABI comment — keep the PK_* tags, header fields
// and per-kind tails mirrored byte-for-byte. The host mirror of every
// routine's MATH lives in bench_interp/tests.rs (`mirror_gate`/`mirror_cache`).
// ===========================================================================

pub(crate) const PK_PRODUCT: u16 = 0;
pub(crate) const PK_MASK_IDENTITY: u16 = 1;
pub(crate) const PK_LOOKUP_PAIR4: u16 = 2;
pub(crate) const PK_LOOKUP_BASE_PAIR: u16 = 3;
pub(crate) const PK_LOOKUP_EXT_PAIR: u16 = 4;
pub(crate) const PK_LOOKUP_BASE_MINUS_MULT: u16 = 5;
pub(crate) const PK_LOOKUP_EXT_MINUS_MULT: u16 = 6;
pub(crate) const PK_LOOKUP_CACHED_DENS: u16 = 7;
pub(crate) const PK_LOOKUP_UNBALANCED_BASE: u16 = 8;
pub(crate) const PK_LOOKUP_UNBALANCED_EXT: u16 = 9;
pub(crate) const PK_VEC_LOOKUP_GATE: u16 = 10;
pub(crate) const PK_MAX_QUADRATIC: u16 = 11;
pub(crate) const PK_CACHE_SINGLE_COLUMN: u16 = 12;
pub(crate) const PK_CACHE_VECTORIZED_LOOKUP: u16 = 13;
pub(crate) const PK_CACHE_MEMORY_TUPLE: u16 = 14;
pub(crate) const PK_CACHE_LOOKUP_SETUP: u16 = 15;

/// Record flags bit 0: the affine tail carries a decoder-select suffix
/// (`e4 fill; u64 pred_ptr`).
pub(crate) const PF_DECODER_SELECT: u16 = 1;

/// Hard cap on NativeK arity the lowering accepts (corpus max is ~37; the
/// kernel streams lanes so this is a sanity bound, not a buffer size).
pub(crate) const MAX_LOWERED_ARITY: usize = 64;

/// Permutation-argument linearization-challenge roles
/// (cs/src/definitions/constants.rs — same indices as gpu_gkr_fwd_generator).
const ADDR_LOW: usize = 0;
const ADDR_HIGH: usize = 1;
const TS_LOW: usize = 2;
const TS_HIGH: usize = 3;
const VAL_LOW: usize = 4;
const VAL_HIGH: usize = 5;

/// All challenge values a forward payload table consumes. For THIS task the
/// values come from the test (random, mirrored host-side); Task 5 swaps in
/// the prover's real challenges.
pub(crate) struct BenchChallenges {
    /// Lookup gamma; the routines read [g, g^2, 2g] from the production
    /// `__constant__ ab_gkr_lookup_gamma_consts` (uploaded by the test).
    pub gamma: E4,
    /// Vector-lookup folding challenge; payloads carry alpha^k * coeff
    /// products, so no alpha constant table is needed device-side.
    pub alpha: E4,
    /// Memory-argument linearization challenges by role (ADDR_LOW..VAL_HIGH).
    pub perm_challenges: [E4; 6],
    /// `permutation_argument_additive_part` (seeds every memory tuple).
    pub perm_additive: E4,
    /// Decoder-lookup fill value (production: alpha^(width-1) * table_id,
    /// staged into a device slot; here an opaque input).
    pub decoder_fill: E4,
}

impl BenchChallenges {
    pub(crate) fn alpha_pow(&self, k: usize) -> E4 {
        let mut acc = E4::ONE;
        for _ in 0..k {
            acc.mul_assign(&self.alpha);
        }
        acc
    }

    /// The `ab_gkr_lookup_gamma_consts` staging triple, exactly as
    /// `stage_lookup_gamma_consts` computes it (flat.cuh:37-42).
    pub(crate) fn gamma_consts(&self) -> [E4; 3] {
        let mut sq = self.gamma;
        sq.mul_assign(&self.gamma);
        let mut dbl = self.gamma;
        dbl.add_assign(&self.gamma);
        [self.gamma, sq, dbl]
    }
}

pub(crate) struct LoweredPayloads {
    /// Record bytes; upload to a 16B-aligned device buffer.
    pub bytes: Vec<u8>,
    /// Byte offset of payload p's record (each 16B-aligned).
    pub offsets: Vec<u32>,
}

fn mont(c: u32) -> BF {
    BF::from_u32_with_reduction(c)
}

fn e4_times_canonical(mut v: E4, c: u32) -> E4 {
    v.mul_assign_by_base(&mont(c));
    v
}

/// Affine lowering of a vector-lookup fold (VectorizedLookup cache /
/// MaterializedVectorLookupInput gate): the alpha-folded column tuple
/// `sum_k alpha^k * (const_k + sum_j c_kj * lane_kj)` becomes one e4 constant
/// plus one e4 coefficient per operand lane, in lane (= lincomb-term) order.
/// Mirrors `emit_vectorized_lookup` (gpu_gkr_fwd_generator/src/lib.rs:282).
pub(crate) fn vec_lookup_affine(columns: &[LinearComb], ch: &BenchChallenges) -> (E4, Vec<E4>) {
    let mut constant = E4::ZERO;
    let mut coeffs = Vec::new();
    for (k, col) in columns.iter().enumerate() {
        let alpha_k = ch.alpha_pow(k);
        constant.add_assign(&e4_times_canonical(alpha_k, col.constant));
        for &(c, _node) in &col.terms {
            coeffs.push(e4_times_canonical(alpha_k, c));
        }
    }
    (constant, coeffs)
}

/// Affine lowering of a memory tuple: `perm_additive + addr_space_term +
/// sum_role chal[role] * column` becomes one e4 constant plus one e4
/// coefficient per operand lane, in `dependencies()` order (= the cache's
/// input-lane order, lower_cache/lower_mem_tuple, codegen_ir.rs:1049-1096).
/// Mirrors `emit_mem_tuple` (gpu_gkr_fwd_generator/src/lib.rs:375) and the
/// production descriptor builder (forward/cache_relation.rs:85+); any
/// descriptor form outside that supported set fails loudly here.
pub(crate) fn mem_tuple_affine(mt: &MemTupleDescriptor, ch: &BenchChallenges) -> (E4, Vec<E4>) {
    let d = &mt.descriptor;
    let mut constant = ch.perm_additive;
    let mut coeffs = vec![E4::ZERO; mt.operands.len()];
    // Lane cursor: dependencies() order is [addr_space dep?, address deps,
    // ts lo, ts hi, val lo, val hi] (cs/src/gkr_compiler/mod.rs:319-348).
    let mut lane = 0usize;
    let mut take = |coeffs: &mut Vec<E4>, add: E4| {
        coeffs[lane].add_assign(&add);
        lane += 1;
    };

    match d.address_space {
        // No challenge on the address-space term (gkr_forward_cache_memory_tuple).
        AddrSpace::Constant(c) => {
            constant.add_assign(&E4::from_base(mont(c)));
        }
        // IsRam -> IS: value += col; IsRegister -> NOT: value += 1 - col
        // (cache_relation.rs:96-107).
        AddrSpace::IsRam(_) => take(&mut coeffs, E4::ONE),
        AddrSpace::IsRegister(_) => {
            constant.add_assign(&E4::ONE);
            let mut neg = E4::ONE;
            neg.negate();
            take(&mut coeffs, neg);
        }
    }

    let chal = |role: usize| ch.perm_challenges[role];
    match &d.address {
        Addr::ConstantU16(c) => {
            constant.add_assign(&e4_times_canonical(chal(ADDR_LOW), *c as u32));
        }
        Addr::Constant(c) => {
            constant.add_assign(&e4_times_canonical(chal(ADDR_LOW), *c));
        }
        Addr::U16Space(_) => take(&mut coeffs, chal(ADDR_LOW)),
        Addr::U32Space(_) => {
            take(&mut coeffs, chal(ADDR_LOW));
            take(&mut coeffs, chal(ADDR_HIGH));
        }
        // dependencies() order is [low_base, high, dyn] (mod.rs:285-300).
        Addr::U32SpaceSpecialIndirect {
            low_dynamic_offset,
            low_offset,
            ..
        } => {
            take(&mut coeffs, chal(ADDR_LOW));
            take(&mut coeffs, chal(ADDR_HIGH));
            if let Some((dyn_coeff, _)) = low_dynamic_offset {
                take(
                    &mut coeffs,
                    e4_times_canonical(chal(ADDR_LOW), *dyn_coeff as u32),
                );
            }
            constant.add_assign(&e4_times_canonical(chal(ADDR_LOW), *low_offset));
        }
        other => panic!("bench lowering: mem-tuple address {other:?} unsupported"),
    }

    match d.timestamp {
        Ts::Zero => {}
        Ts::Normal(_) => {
            take(&mut coeffs, chal(TS_LOW));
            constant.add_assign(&e4_times_canonical(chal(TS_LOW), d.timestamp_offset));
            take(&mut coeffs, chal(TS_HIGH));
        }
    }

    match d.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(_) => {
            take(&mut coeffs, chal(VAL_LOW));
            take(&mut coeffs, chal(VAL_HIGH));
        }
        RamWordRepresentation::U8Limbs(_) => {
            panic!("bench lowering: mem-tuple U8Limbs value unsupported (census subset)")
        }
    }

    assert_eq!(
        lane,
        mt.operands.len(),
        "mem-tuple lane walk diverged from operands"
    );
    (constant, coeffs)
}

/// bf lincomb lowering for SingleColumnLookup caches: Montgomery-form
/// constant + per-lane coefficients in term order.
pub(crate) fn lincomb_bf(lc: &LinearComb) -> (BF, Vec<BF>) {
    (
        mont(lc.constant),
        lc.terms.iter().map(|&(c, _)| mont(c)).collect(),
    )
}

/// (kind tag, expected dst count, expected operand-lane count).
pub(crate) fn payload_kind_shape(rec: &PayloadRecord) -> (u16, usize, usize) {
    match rec {
        PayloadRecord::Gate(g) => match &g.kind {
            GateKind::TrivialProduct { .. } | GateKind::InitialGrandProductFromCaches { .. } => {
                (PK_PRODUCT, 1, 2)
            }
            GateKind::MaskIntoIdentityProduct { .. } => (PK_MASK_IDENTITY, 1, 2),
            GateKind::AggregateLookupRationalPair { .. } => (PK_LOOKUP_PAIR4, 2, 4),
            GateKind::LookupPairFromMaterializedBaseInputs { .. } => (PK_LOOKUP_BASE_PAIR, 2, 2),
            GateKind::LookupPairFromMaterializedVectorInputs { .. } => (PK_LOOKUP_EXT_PAIR, 2, 2),
            GateKind::LookupFromMaterializedBaseInputWithSetup { .. } => {
                (PK_LOOKUP_BASE_MINUS_MULT, 2, 3)
            }
            GateKind::LookupFromMaterializedVectorInputWithSetup { .. } => {
                (PK_LOOKUP_EXT_MINUS_MULT, 2, 3)
            }
            GateKind::LookupWithCachedDensAndSetup { .. } => (PK_LOOKUP_CACHED_DENS, 2, 4),
            GateKind::LookupUnbalancedPairWithMaterializedBaseInputs { .. } => {
                (PK_LOOKUP_UNBALANCED_BASE, 2, 3)
            }
            GateKind::LookupUnbalancedPairWithMaterializedVectorInputs { .. } => {
                (PK_LOOKUP_UNBALANCED_EXT, 2, 3)
            }
            GateKind::MaterializedVectorLookupInput { input } => (
                PK_VEC_LOOKUP_GATE,
                1,
                input.columns.iter().map(|c| c.terms.len()).sum(),
            ),
            GateKind::MaxQuadratic { flat, .. } => (
                PK_MAX_QUADRATIC,
                1,
                flat.quadratic
                    .iter()
                    .map(|(_, terms)| 1 + terms.len())
                    .sum::<usize>()
                    + flat.linear.len(),
            ),
            other => panic!(
                "bench lowering: gate kind outside the Task-0 census: {:?}",
                std::mem::discriminant(other)
            ),
        },
        PayloadRecord::Cache(c) => match &c.kind {
            CacheKind::SingleColumnLookup { column, .. } => {
                (PK_CACHE_SINGLE_COLUMN, 1, column.terms.len())
            }
            CacheKind::VectorizedLookup { columns, .. } => (
                PK_CACHE_VECTORIZED_LOOKUP,
                1,
                columns.iter().map(|c| c.terms.len()).sum(),
            ),
            CacheKind::MemoryTuple { descriptor } => {
                (PK_CACHE_MEMORY_TUPLE, 1, descriptor.operands.len())
            }
            CacheKind::VectorizedLookupSetup => (PK_CACHE_LOOKUP_SETUP, 1, c.inputs.len()),
        },
    }
}

/// Element width of payload dst slot j: true = e4 column, false = bf column.
/// Kind-implied (matches the kernel's stores); cross-checked against the IR
/// dst node domain in `lower_payloads`.
pub(crate) fn payload_dst_e4(rec: &PayloadRecord, _j: usize) -> bool {
    let (kind, ..) = payload_kind_shape(rec);
    !matches!(kind, PK_MAX_QUADRATIC | PK_CACHE_SINGLE_COLUMN)
}

struct RecWriter {
    bytes: Vec<u8>,
}

impl RecWriter {
    fn pad16(&mut self) {
        while self.bytes.len() % 16 != 0 {
            self.bytes.push(0);
        }
    }
    fn u16(&mut self, v: u16) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }
    fn u32(&mut self, v: u32) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }
    fn u64(&mut self, v: u64) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }
    fn bf(&mut self, v: BF) {
        self.u32(v.0);
    }
    fn e4(&mut self, v: E4) {
        assert_eq!(self.bytes.len() % 16, 0, "e4 field must be 16B-aligned");
        // E4 = BabyBearExt4: 4 Montgomery bf limbs, layout-compatible with the
        // device e4 (the same bytes the H2D source-column copies rely on).
        let limbs: [u32; 4] = unsafe { std::mem::transmute(v) };
        for l in limbs {
            self.u32(l);
        }
    }
}

fn arena_domain(arena: &[ExprNode], node: u32) -> Domain {
    match &arena[node as usize] {
        ExprNode::Place { domain, .. } | ExprNode::GateOutput { domain, .. } => *domain,
        ExprNode::Constant(_) => Domain::Base,
        ExprNode::Sum { domain, .. } | ExprNode::Product { domain, .. } => *domain,
    }
}

/// Lower `cf.payloads` into the device record buffer.
///
/// Resolver contract (test-owned now; Task 5 swaps in prover pointers):
/// - `resolve_dst(p, rec, j)`: device column base for payload p's j-th output
///   (gates: `g.dst[j]`; caches: the cache out column). Element width is
///   `payload_dst_e4(rec, j)`.
/// - `resolve_decoder_pred(p, rec)`: bf execute-predicate column for decoder
///   vector lookups (`lookup_set_index == usize::MAX`); never called otherwise.
/// - `resolve_setup_table(cache_idx)`: (e4 table base, valid length) for
///   `VectorizedLookupSetup` caches.
pub(crate) fn lower_payloads(
    cf: &CompiledForward,
    arena: &[ExprNode],
    resolve_dst: impl Fn(usize, &PayloadRecord, usize) -> *mut u8,
    resolve_decoder_pred: impl Fn(usize, &PayloadRecord) -> *const u8,
    resolve_setup_table: impl Fn(usize) -> (*const u8, u32),
    ch: &BenchChallenges,
) -> LoweredPayloads {
    let mut w = RecWriter { bytes: Vec::new() };
    let mut offsets = Vec::with_capacity(cf.payloads.len());

    for (p, rec) in cf.payloads.iter().enumerate() {
        let (kind, n_dsts, n_ops) = payload_kind_shape(rec);
        assert_eq!(
            n_ops,
            cf.payload_operands[p].len(),
            "payload {p}: kind-shape operand count vs payload_operands"
        );
        assert!(
            n_ops <= MAX_LOWERED_ARITY,
            "payload {p}: arity {n_ops} > cap"
        );

        // Decoder-select tail applies to alpha-folded lookups with the formal
        // decoder set index (usize::MAX round-trips JSON as a huge u64).
        let decoder = match rec {
            PayloadRecord::Gate(g) => match &g.kind {
                GateKind::MaterializedVectorLookupInput { input } => {
                    input.lookup_set_index == usize::MAX
                }
                _ => false,
            },
            PayloadRecord::Cache(c) => match &c.kind {
                CacheKind::VectorizedLookup {
                    lookup_set_index, ..
                } => *lookup_set_index == usize::MAX,
                _ => false,
            },
        };

        let (num_challenges, powers): (u32, Vec<u32>) = match rec {
            PayloadRecord::Gate(g) => {
                assert_eq!(
                    g.batch_terms.len(),
                    g.num_challenges as usize,
                    "payload {p}: batch_terms vs num_challenges"
                );
                // ABSOLUTE batch powers (assign_batch_powers, codegen_ir.rs).
                // ABI-fidelity only: forward routines never consume them.
                (
                    g.num_challenges as u32,
                    g.batch_terms.iter().map(|t| t.power).collect(),
                )
            }
            PayloadRecord::Cache(_) => (0, Vec::new()),
        };

        // IR dst-domain cross-check against the kind-implied store width.
        if let PayloadRecord::Gate(g) = rec {
            assert_eq!(g.dst.len(), n_dsts, "payload {p}: gate dst count");
            for (j, slot) in g.dst.iter().enumerate() {
                let want_e4 = payload_dst_e4(rec, j);
                let got_e4 = arena_domain(arena, slot.node.0) == Domain::Ext;
                assert_eq!(got_e4, want_e4, "payload {p}: dst {j} domain vs kind width");
            }
        } else if let PayloadRecord::Cache(c) = rec {
            let want_e4 = payload_dst_e4(rec, 0);
            let got_e4 = arena_domain(arena, c.out.0 .0) == Domain::Ext;
            assert_eq!(
                got_e4, want_e4,
                "payload {p}: cache out domain vs kind width"
            );
        }

        w.pad16();
        offsets.push(w.bytes.len() as u32);

        // Header (see the ABI comment in the .cu).
        w.u16(kind);
        w.u16(n_dsts as u16);
        w.u16(n_ops as u16);
        w.u16(if decoder { PF_DECODER_SELECT } else { 0 });
        w.u32(num_challenges);
        w.u32(0); // pad
        for j in 0..n_dsts {
            let ptr = resolve_dst(p, rec, j);
            assert!(!ptr.is_null(), "payload {p}: null dst {j}");
            w.u64(ptr as u64);
        }
        for pw in powers {
            w.u32(pw);
        }

        // Per-kind tail.
        match kind {
            PK_VEC_LOOKUP_GATE | PK_CACHE_VECTORIZED_LOOKUP | PK_CACHE_MEMORY_TUPLE => {
                let (constant, coeffs) = match rec {
                    PayloadRecord::Gate(g) => match &g.kind {
                        GateKind::MaterializedVectorLookupInput { input } => {
                            vec_lookup_affine(&input.columns, ch)
                        }
                        _ => unreachable!(),
                    },
                    PayloadRecord::Cache(c) => match &c.kind {
                        CacheKind::VectorizedLookup { columns, .. } => {
                            vec_lookup_affine(columns, ch)
                        }
                        CacheKind::MemoryTuple { descriptor } => mem_tuple_affine(descriptor, ch),
                        _ => unreachable!(),
                    },
                };
                assert_eq!(coeffs.len(), n_ops, "payload {p}: affine coeff count");
                w.pad16();
                w.e4(constant);
                for c in coeffs {
                    w.e4(c);
                }
                if decoder {
                    w.e4(ch.decoder_fill);
                    let pred = resolve_decoder_pred(p, rec);
                    assert!(!pred.is_null(), "payload {p}: null decoder predicate");
                    w.u64(pred as u64);
                }
            }
            PK_CACHE_SINGLE_COLUMN => {
                let column = match rec {
                    PayloadRecord::Cache(c) => match &c.kind {
                        CacheKind::SingleColumnLookup { column, .. } => column,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };
                let (constant, coeffs) = lincomb_bf(column);
                w.bf(constant);
                for c in coeffs {
                    w.bf(c);
                }
            }
            PK_CACHE_LOOKUP_SETUP => {
                let ci = match cf.program.payloads[p].cache {
                    Some(ci) => ci as usize,
                    None => panic!("payload {p}: lookup-setup payload without cache index"),
                };
                let (table, len) = resolve_setup_table(ci);
                assert!(!table.is_null(), "payload {p}: null setup table");
                w.u64(table as u64);
                w.u32(len);
            }
            PK_MAX_QUADRATIC => {
                let flat = match rec {
                    PayloadRecord::Gate(g) => match &g.kind {
                        GateKind::MaxQuadratic { flat, .. } => flat,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };
                w.u32(flat.quadratic.len() as u32);
                w.u32(flat.linear.len() as u32);
                w.bf(mont(flat.constant));
                for (_a, terms) in &flat.quadratic {
                    w.u32(terms.len() as u32);
                    for &(c, _b) in terms {
                        w.bf(mont(c));
                    }
                }
                for &(c, _a) in &flat.linear {
                    w.bf(mont(c));
                }
            }
            _ => {} // simple gate kinds: gamma rides the __constant__ symbol
        }
    }

    let lp = LoweredPayloads {
        bytes: w.bytes,
        offsets,
    };
    verify_lowered_payloads(&lp, cf);
    lp
}

/// Pointers re-read from a lowered payload's record bytes — the same u64
/// fields `verify_lowered_payloads` walks past. Lets the harness's structural
/// gate (b) assert the embedded pointers match the resolver's GKRAddress
/// resolution byte-for-byte, without re-plumbing the lowering's closures.
pub(crate) struct LoweredPayloadPointers {
    /// One device base per dst slot j (the `u64` written at `off + 16 + 8*j`).
    pub dsts: Vec<u64>,
    /// `VectorizedLookupSetup` table base (`PK_CACHE_LOOKUP_SETUP` tail); else None.
    pub setup_table: Option<u64>,
    /// Decoder execute-predicate base (affine tail decoder-select suffix); else None.
    pub decoder_pred: Option<u64>,
}

/// Re-read payload `p`'s embedded pointers from `lp.bytes`, mirroring the
/// device reader's cursor arithmetic (the SAME walk as `verify_lowered_payloads`).
pub(crate) fn lowered_payload_pointers(lp: &LoweredPayloads, p: usize) -> LoweredPayloadPointers {
    let rd_u16 = |off: usize| u16::from_le_bytes(lp.bytes[off..off + 2].try_into().unwrap());
    let rd_u32 = |off: usize| u32::from_le_bytes(lp.bytes[off..off + 4].try_into().unwrap());
    let rd_u64 = |off: usize| u64::from_le_bytes(lp.bytes[off..off + 8].try_into().unwrap());

    let off = lp.offsets[p] as usize;
    let kind = rd_u16(off);
    let n_dsts = rd_u16(off + 2) as usize;
    let n_ops = rd_u16(off + 4) as usize;
    let flags = rd_u16(off + 6);
    let num_challenges = rd_u32(off + 8) as usize;

    let dsts: Vec<u64> = (0..n_dsts).map(|j| rd_u64(off + 16 + 8 * j)).collect();

    // Cursor past header + dst pointers + powers — the start of the per-kind tail.
    let mut cur = off + 16 + 8 * n_dsts + 4 * num_challenges;
    let mut setup_table = None;
    let mut decoder_pred = None;
    match kind {
        PK_VEC_LOOKUP_GATE | PK_CACHE_VECTORIZED_LOOKUP | PK_CACHE_MEMORY_TUPLE => {
            cur = (cur + 15) & !15;
            cur += 16 * (1 + n_ops); // constant + per-lane coeffs (e4)
            if flags & PF_DECODER_SELECT != 0 {
                cur += 16; // decoder-fill e4
                decoder_pred = Some(rd_u64(cur));
            }
        }
        PK_CACHE_LOOKUP_SETUP => {
            setup_table = Some(rd_u64(cur));
        }
        _ => {}
    }
    LoweredPayloadPointers {
        dsts,
        setup_table,
        decoder_pred,
    }
}

/// Structural cross-check: re-parse the byte buffer with an independent
/// host-side cursor mirroring the device reader, asserting per payload that
/// the kind tag matches the `PayloadRecord` variant, the dst count matches
/// the record's dst len, and the operand count matches
/// `payload_operands[p].len()`.
pub(crate) fn verify_lowered_payloads(lp: &LoweredPayloads, cf: &CompiledForward) {
    assert_eq!(lp.offsets.len(), cf.payloads.len());
    let rd_u16 = |off: usize| u16::from_le_bytes(lp.bytes[off..off + 2].try_into().unwrap());
    let rd_u32 = |off: usize| u32::from_le_bytes(lp.bytes[off..off + 4].try_into().unwrap());
    for (p, rec) in cf.payloads.iter().enumerate() {
        let off = lp.offsets[p] as usize;
        assert_eq!(off % 16, 0, "payload {p}: record not 16B-aligned");
        let (want_kind, want_dsts, _) = payload_kind_shape(rec);
        let kind = rd_u16(off);
        let n_dsts = rd_u16(off + 2) as usize;
        let n_ops = rd_u16(off + 4) as usize;
        let flags = rd_u16(off + 6);
        let num_challenges = rd_u32(off + 8) as usize;
        assert_eq!(kind, want_kind, "payload {p}: kind tag");
        assert_eq!(n_dsts, want_dsts, "payload {p}: dst count");
        if let PayloadRecord::Gate(g) = rec {
            assert_eq!(n_dsts, g.dst.len(), "payload {p}: record dst len");
            assert_eq!(num_challenges, g.batch_terms.len(), "payload {p}: powers");
        }
        assert_eq!(
            n_ops,
            cf.payload_operands[p].len(),
            "payload {p}: operand count"
        );
        // Walk the record to its end with the device's cursor arithmetic and
        // bound it by the next record's offset (or the buffer end).
        let mut cur = off + 16 + 8 * n_dsts + 4 * num_challenges;
        match kind {
            PK_VEC_LOOKUP_GATE | PK_CACHE_VECTORIZED_LOOKUP | PK_CACHE_MEMORY_TUPLE => {
                cur = (cur + 15) & !15;
                cur += 16 * (1 + n_ops);
                if flags & PF_DECODER_SELECT != 0 {
                    cur += 16 + 8;
                }
            }
            PK_CACHE_SINGLE_COLUMN => cur += 4 * (1 + n_ops),
            PK_CACHE_LOOKUP_SETUP => cur += 12,
            PK_MAX_QUADRATIC => {
                let n_quad = rd_u32(cur) as usize;
                let n_lin = rd_u32(cur + 4) as usize;
                cur += 12;
                let mut lanes = 0usize;
                for _ in 0..n_quad {
                    let n_sub = rd_u32(cur) as usize;
                    cur += 4 + 4 * n_sub;
                    lanes += 1 + n_sub;
                }
                cur += 4 * n_lin;
                lanes += n_lin;
                assert_eq!(lanes, n_ops, "payload {p}: MQ lane walk");
            }
            _ => {}
        }
        let bound = lp
            .offsets
            .get(p + 1)
            .map(|&o| o as usize)
            .unwrap_or(lp.bytes.len());
        assert!(cur <= bound, "payload {p}: record overruns its slot");
    }
}
