//! Generates specialized, CSE-exploiting, per-row CUDA forward kernels for GKR
//! layers from the codegen IR (`cs::gkr_compiler::codegen_ir`).
//!
//! Mirrors `gpu_witness_eval_generator`: the Rust side walks the per-layer SSA
//! arena and emits a compact macro-DSL `.cuh`. Common subexpressions (here: base
//! column loads and cache values) are emitted exactly once. The heavy `bf`/`e4`
//! arithmetic + `gkr_eval_*` calls + column addressing live in the hand-written
//! `gkr_forward_generation.cuh` macro header that consumes this output.
//!
//! Scope (forward pass): the live forward DAG is `base Place loads -> caches ->
//! output gates`. The arena `Sum`/`Product`/`Constant` nodes are the MaxQuad
//! *constraint* expressions, consumed only by the no-output
//! `EnforceSingleMaxQuadraticConstraint` gates — they produce NOTHING in the
//! forward pass, so this generator never emits them (and panics defensively if a
//! forward output is ever found to depend on one).

use cs::definitions::gkr::RamWordRepresentation as Word;
use cs::definitions::{GKRAddress, VirtualSetupPoly};
use cs::gkr_compiler::codegen_ir::{
    CacheKind, CodegenCache, CodegenGate, CodegenGlobals, CodegenLayer, Domain, ExprNode, GateKind,
    LinearComb, MemTupleDescriptor, NodeId,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict as AddrSpace, CompiledAddressStrict as Addr,
    CompiledMemoryTimestamp as Ts,
};
use gpu_gkr_model::storage_layout::{GpuGKRStorageLayout, address_storage_layer};

/// Concrete base field of the lowered circuits (BabyBear). The codegen IR is
/// field-erased (`u32` constants), so this is only used at the edges.
pub type F = ::field::baby_bear::base::BabyBearField;

/// BabyBear prime (0x78000001) and its `-1` representative. Special-cased in
/// codegen so `×1`/`×(-1)`/`×0` never emit a Montgomery multiply.
const ORDER: u32 = 0x7800_0001;
const NEG_ONE: u32 = ORDER - 1;

// Permutation-argument linearization-challenge roles (cs/src/definitions/constants.rs:15-20).
const ADDR_LOW: u32 = 0;
const ADDR_HIGH: u32 = 1;
const TS_LOW: u32 = 2;
const TS_HIGH: u32 = 3;
const VAL_LOW: u32 = 4;
const VAL_HIGH: u32 = 5;

/// A host-side copy alias recorded for the launcher: `output` address is a view
/// alias of `input` address (a `CopyIn*` gate — no kernel work). Mirrors the
/// prover's `aliased_*_outputs` (gpu .../forward/flat_plan.rs:131-138).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CopyAlias {
    pub output: GKRAddress,
    pub input: GKRAddress,
}

/// Result of emitting one layer's forward kernel: the macro-DSL body plus the
/// host-side launch manifest the device code cannot carry.
#[derive(Clone, Debug)]
pub struct EmittedLayer {
    /// The `.cuh` body (a single `fwd_layer_<L>` function, between
    /// `FWD_FN_BEGIN`/`FWD_FN_END`).
    pub cuh: String,
    /// `CopyIn*` aliases the host launcher must wire (output view = input view).
    pub copy_aliases: Vec<CopyAlias>,
}

/// Emit the macro-DSL `.cuh` body for one layer's forward kernel.
///
/// `layout` is the GPU storage layout built from the SAME compiled artifact
/// this codegen IR was lowered from (`GpuGKRStorageLayout::from_artifact*`). It
/// is the single source of truth for the column (`poly_idx`) each output is
/// written at in its consolidated per-`(layer, class, field)` backing. Emitting
/// `STORE_*` at `poly_idx` (not the raw `GKRAddress` offset) lets the prover
/// pass the consolidated backing base pointers straight into the kernel proxy —
/// no per-output scratch buffer and no D2D scatter. The mapping is identical to
/// what `GpuGKRStorage::allocate_*_view` resolves at run time, so the kernel
/// writes land exactly where the rest of the prover reads them.
pub fn emit_layer_forward(
    layer: &CodegenLayer,
    globals: &CodegenGlobals,
    layer_idx: usize,
    layout: &GpuGKRStorageLayout,
) -> EmittedLayer {
    let mut g = Generator::new(globals, layer_idx, layout);
    g.emit(layer);
    g.finish()
}

struct Generator<'a> {
    #[allow(dead_code)]
    globals: &'a CodegenGlobals,
    layer_idx: usize,
    /// Storage layout: resolves each output `GKRAddress` to its dense `poly_idx`
    /// column within its consolidated backing (see `emit_layer_forward`).
    layout: &'a GpuGKRStorageLayout,
    out: String,
    tmp: usize,
    /// Var names already emitted for loaded columns (CSE — one load per
    /// physical column, keyed by the var name `m{col}`/`w{col}`/`rc16`/...).
    loaded: std::collections::HashSet<String>,
    /// `Cached{0,off}` -> the var name holding that cache's value this row.
    cache_var: std::collections::HashMap<usize, String>,
    copy_aliases: Vec<CopyAlias>,
}

impl<'a> Generator<'a> {
    fn new(globals: &'a CodegenGlobals, layer_idx: usize, layout: &'a GpuGKRStorageLayout) -> Self {
        Self {
            globals,
            layer_idx,
            layout,
            out: String::new(),
            tmp: 0,
            loaded: Default::default(),
            cache_var: Default::default(),
            copy_aliases: Vec::new(),
        }
    }

    /// Dense `poly_idx` column for an output address, from the storage layout.
    /// This is the column the kernel must store into so the prover's
    /// consolidated backing (passed as the proxy base pointer) lines up with
    /// what `allocate_*_view` hands the rest of the pipeline.
    fn poly_idx_of(&self, addr: GKRAddress) -> u32 {
        let storage_layer = address_storage_layer(addr);
        self.layout
            .lookup(storage_layer, &addr)
            .unwrap_or_else(|| {
                panic!("output {addr:?} (storage layer {storage_layer}) missing from layout")
            })
            .3
    }

    fn line(&mut self, s: String) {
        self.out.push_str(&s);
        self.out.push('\n');
    }

    fn fresh(&mut self) -> String {
        let v = format!("t{}", self.tmp);
        self.tmp += 1;
        v
    }

    fn emit(&mut self, layer: &CodegenLayer) {
        self.line(format!("FWD_FN_BEGIN({})", self.layer_idx));
        // 1. caches first (their values feed same-layer gates via Cached re-reads)
        for (idx, cache) in layer.caches.iter().enumerate() {
            self.emit_cache(layer, idx, cache);
        }
        // 2. output-bearing gates (and copy aliases). MaxQuad constraints emit nothing.
        for gate in &layer.gates {
            self.emit_gate(layer, gate);
        }
        for gate in &layer.gates_external {
            self.emit_gate(layer, gate);
        }
        self.line("FWD_FN_END".to_string());
    }

    // -- operand resolution -------------------------------------------------

    /// Resolve an operand `NodeId` to the CUDA var name holding its value,
    /// emitting a base-column load on first use. Panics on a forward-dead node
    /// kind (Sum/Product/Constant) — those are constraint-only and must never be
    /// reachable from a forward output.
    fn operand(&mut self, layer: &CodegenLayer, id: NodeId) -> String {
        match &layer.arena.nodes[id.0 as usize] {
            ExprNode::Place { addr, .. } => self.place_var(*addr),
            ExprNode::GateOutput { .. } => {
                // A produced value referenced directly (no gate->gate edges in
                // layer 0). If this fires for caches, the producer var must
                // already be recorded; otherwise it's an unhandled producer edge.
                panic!(
                    "forward codegen: direct GateOutput operand (node {}) not supported yet",
                    id.0
                )
            }
            other => panic!(
                "forward codegen: forward output depends on a constraint-only node {} ({:?}); \
                 the forward pass must not evaluate Sum/Product/Constant arena nodes",
                id.0, other
            ),
        }
    }

    /// Resolve a `Place` address to its CUDA var. Loads are keyed by the
    /// PHYSICAL column (`m{col}`/`w{col}`/`s{col}`/`rc16`/`rcts`), so a column
    /// referenced both by a memory-tuple and by a gate/lincomb loads exactly
    /// once (full cross-relation CSE).
    fn place_var(&mut self, addr: GKRAddress) -> String {
        match addr {
            GKRAddress::Cached { layer, offset } => {
                debug_assert_eq!(layer, self.layer_idx, "cross-layer Cached read");
                self.cache_var
                    .get(&offset)
                    .cloned()
                    .unwrap_or_else(|| panic!("Cached{{{layer},{offset}}} read before produced"))
            }
            GKRAddress::BaseLayerMemory(c) => self.col_load('m', "LOAD_MEM", c),
            GKRAddress::BaseLayerWitness(c) => self.col_load('w', "LOAD_WIT", c),
            GKRAddress::Setup(c) => self.col_load('s', "LOAD_SETUP", c),
            GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits) => {
                self.virt_load("rc16", "LOAD_RC16")
            }
            GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp) => {
                self.virt_load("rcts", "LOAD_RCTS")
            }
            other => panic!("forward codegen: unsupported input address {:?}", other),
        }
    }

    /// Load a base column once, var = `{prefix}{col}` (e.g. `m4`).
    fn col_load(&mut self, prefix: char, macro_name: &str, col: usize) -> String {
        let v = format!("{prefix}{col}");
        if self.loaded.insert(v.clone()) {
            self.line(format!("{macro_name}({v}, {col})"));
        }
        v
    }

    /// Materialize a virtual base column (range check) once, var = `name`.
    fn virt_load(&mut self, name: &str, macro_name: &str) -> String {
        if self.loaded.insert(name.to_string()) {
            self.line(format!("{macro_name}({name})"));
        }
        name.to_string()
    }

    // -- caches -------------------------------------------------------------

    fn emit_cache(&mut self, layer: &CodegenLayer, idx: usize, cache: &CodegenCache) {
        let off = match cache.out.1 {
            GKRAddress::Cached { offset, .. } => offset,
            other => panic!("cache {idx} out addr not Cached: {:?}", other),
        };
        // Each cache value is emitted into a temp var; that var (not a separate
        // ALIAS) becomes the cache's value for same-layer consumers.
        let (v, ext) = match &cache.kind {
            CacheKind::SingleColumnLookup { column, .. } => {
                (self.emit_lincomb_base(layer, column), false)
            }
            CacheKind::VectorizedLookupSetup => {
                let t = self.fresh();
                self.line(format!("LOOKUP_SETUP({t})"));
                (t, true)
            }
            CacheKind::MemoryTuple { descriptor } => (self.emit_mem_tuple(layer, descriptor), true),
            CacheKind::VectorizedLookup {
                columns,
                lookup_set_index,
            } => (
                self.emit_vectorized_lookup(layer, columns, *lookup_set_index),
                true,
            ),
        };
        // Store at the layout's dense `poly_idx` column (not the raw offset) so
        // the kernel writes directly into the prover's consolidated cache
        // backing. `off` still keys `cache_var` for same-layer `Cached{0,off}`
        // re-reads.
        let poly_idx = self.poly_idx_of(cache.out.1);
        if ext {
            self.line(format!("STORE_CACHE_EXT({poly_idx}, {v})"));
        } else {
            self.line(format!("STORE_CACHE_BASE({poly_idx}, {v})"));
        }
        self.cache_var.insert(off, v);
    }

    /// Emit a vectorized-lookup cache value: the alpha-folded column tuple
    /// `Σ_k alpha^k · col_k` (ext). For the decoder lookup
    /// (`lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX == usize::MAX`) the
    /// tuple is predicate-selected against the precomputed fill scalar
    /// (`alpha^(width-1) · Decoder`) on non-executing rows.
    ///
    /// Stays in base as long as possible: every column is built in base
    /// (`emit_lincomb_base`); `col_0` (weight `alpha^0 = 1`) is a plain base→ext
    /// lift with no multiply; each `col_k` (k≥1) crosses into ext only via the
    /// mixed `E_FMA_ALPHA` (`ext alpha^k · base col_k + ext acc`), never a full
    /// ext×ext multiply. `alpha^k` lives in a device-constant power array indexed
    /// by `k` (host-folded; alpha is a runtime Fiat-Shamir challenge), mirroring
    /// the existing GPU setup path's `ab_gkr_lookup_alpha_powers`.
    fn emit_vectorized_lookup(
        &mut self,
        layer: &CodegenLayer,
        columns: &[LinearComb],
        lookup_set_index: usize,
    ) -> String {
        // col_0: base→ext lift, alpha^0 = 1 (no Montgomery multiply).
        let b0 = self.emit_lincomb_base(layer, &columns[0]);
        let mut acc = self.fresh();
        self.line(format!("E_FROM_BASE({acc}, {b0})"));
        // col_k (k≥1): ext acc += alpha^k · base col_k (mixed fma).
        for (k, col) in columns.iter().enumerate().skip(1) {
            let bk = self.emit_lincomb_base(layer, col);
            let t = self.fresh();
            self.line(format!("E_FMA_ALPHA({t}, {k}, {bk}, {acc})"));
            acc = t;
        }
        // Decoder lookup: on non-executing (padding) rows the tuple is replaced
        // by the precomputed fill scalar. The `execute` predicate is a base-layer
        // boolean column (prover: GKRAddress::BaseLayerMemory(machine_state.execute));
        // the fill (alpha^(width-1)·Decoder) is read from the same device slot the
        // existing GPU setup prelude already populates.
        if lookup_set_index == usize::MAX {
            let exec = self
                .globals
                .memory_layout
                .machine_state
                .as_ref()
                .expect("decoder VectorizedLookup requires machine_state.execute predicate")
                .execute;
            let p = self.place_var(GKRAddress::BaseLayerMemory(exec));
            let t = self.fresh();
            self.line(format!("SELECT_DECODER_FILL({t}, {p}, {acc})"));
            acc = t;
        }
        acc
    }

    /// Emit `constant + Σ coeff_k * operand_k` in the base field; return the var.
    /// Constants 0/1/(-1) are special-cased (no Montgomery multiply); a zero
    /// constant emits no `+0` init (the first nonzero term seeds the accumulator).
    fn emit_lincomb_base(&mut self, layer: &CodegenLayer, lc: &LinearComb) -> String {
        let mut acc: Option<String> = if lc.constant != 0 {
            let t = self.fresh();
            self.line(format!("BF_CONST({t}, {})", lc.constant));
            Some(t)
        } else {
            None
        };
        for (coeff, node) in &lc.terms {
            let c = *coeff;
            if c == 0 {
                continue; // ×0: drop the term
            }
            let src = self.operand(layer, *node);
            acc = Some(match (acc.take(), c) {
                (None, 1) => src, // first term, +acc=col: just become the column
                (None, c) if c == NEG_ONE => {
                    let t = self.fresh();
                    self.line(format!("BF_NEG({t}, {src})"));
                    t
                }
                (None, c) => {
                    let t = self.fresh();
                    self.line(format!("BF_MULC({t}, {c}, {src})"));
                    t
                }
                (Some(a), 1) => {
                    let t = self.fresh();
                    self.line(format!("BF_ADD({t}, {src}, {a})"));
                    t
                }
                (Some(a), c) if c == NEG_ONE => {
                    let t = self.fresh();
                    self.line(format!("BF_SUB({t}, {a}, {src})")); // a - col
                    t
                }
                (Some(a), c) => {
                    let t = self.fresh();
                    self.line(format!("BF_FMAC({t}, {c}, {src}, {a})"));
                    t
                }
            });
        }
        acc.unwrap_or_else(|| {
            let t = self.fresh();
            self.line(format!("BF_CONST({t}, 0)"));
            t
        })
    }

    /// Emit a memory-tuple value: `perm_additive + addr_space_term +
    /// Σ_role chal[role]·column`. Layer-0 subset; unsupported arms panic.
    fn emit_mem_tuple(&mut self, layer: &CodegenLayer, mt: &MemTupleDescriptor) -> String {
        let d = &mt.descriptor;
        let mut acc = self.fresh();
        self.line(format!("E_FROM_PERM_ADD({acc})"));

        // address-space affine term (no challenge)
        match d.address_space {
            AddrSpace::Constant(0) => {}
            AddrSpace::Constant(c) => {
                let next = self.fresh();
                self.line(format!("E_ADD_BFC({next}, {acc}, {c})"));
                acc = next;
            }
            other => panic!(
                "forward codegen: mem-tuple address_space {:?} unsupported",
                other
            ),
        }

        // address term(s)
        acc = match &d.address {
            Addr::ConstantU16(c) => self.fma_const(acc, ADDR_LOW, *c as u32),
            Addr::Constant(c) => self.fma_const(acc, ADDR_LOW, *c),
            Addr::U16Space(off) => self.fma_mem(layer, acc, ADDR_LOW, *off),
            Addr::U32Space([lo, hi]) => {
                let a = self.fma_mem(layer, acc, ADDR_LOW, *lo);
                self.fma_mem(layer, a, ADDR_HIGH, *hi)
            }
            // Delegation register/indirect addressing: the LOW limb is
            // `mem[low_base] + dyn_coeff·mem[dyn_col] + low_offset` (all base
            // field), folded onto the ADDR_LOW challenge; the HIGH limb is
            // `mem[high]` on ADDR_HIGH (cs/src/gkr_compiler/mod.rs:285).
            Addr::U32SpaceSpecialIndirect {
                low_base,
                low_dynamic_offset,
                low_offset,
                high,
            } => {
                // ADDR_LOW base column.
                let mut a = self.fma_mem(layer, acc, ADDR_LOW, *low_base);
                // ADDR_LOW dynamic term: chal[ADDR_LOW]·(dyn_coeff·mem[dyn_col]).
                if let Some((dyn_coeff, dyn_col)) = low_dynamic_offset {
                    let src = self.ensure_mem_load(*dyn_col);
                    let scaled = self.fresh();
                    self.line(format!("BF_MULC({scaled}, {}, {src})", *dyn_coeff as u32));
                    let next = self.fresh();
                    self.line(format!("E_FMA_PERM({next}, {ADDR_LOW}, {scaled}, {a})"));
                    a = next;
                }
                // ADDR_LOW constant offset (fma_const drops it when 0).
                a = self.fma_const(a, ADDR_LOW, *low_offset);
                // ADDR_HIGH base column.
                self.fma_mem(layer, a, ADDR_HIGH, *high)
            }
            other => panic!("forward codegen: mem-tuple address {:?} unsupported", other),
        };

        // timestamp term(s)
        acc = match d.timestamp {
            Ts::Zero => acc,
            Ts::Normal([ts_low, ts_high]) => {
                let a = self.fma_mem(layer, acc, TS_LOW, ts_low);
                let a = if d.timestamp_offset != 0 {
                    self.fma_const(a, TS_LOW, d.timestamp_offset)
                } else {
                    a
                };
                self.fma_mem(layer, a, TS_HIGH, ts_high)
            }
        };

        // value term(s)
        acc = match d.value {
            Word::Zero => acc,
            Word::U16Limbs([v_low, v_high]) => {
                let a = self.fma_mem(layer, acc, VAL_LOW, v_low);
                self.fma_mem(layer, a, VAL_HIGH, v_high)
            }
            Word::U8Limbs(_) => {
                panic!("forward codegen: mem-tuple U8Limbs value unsupported (layer-0 subset)")
            }
        };
        acc
    }

    /// `acc = e4::fma(perm_lin[role], load_mem(off), acc)`.
    fn fma_mem(&mut self, layer: &CodegenLayer, acc: String, role: u32, off: usize) -> String {
        // memory-tuple columns are always BaseLayerMemory; load (CSE'd by column).
        let src = self.ensure_mem_load(off);
        let next = self.fresh();
        self.line(format!("E_FMA_PERM({next}, {role}, {src}, {acc})"));
        let _ = layer;
        next
    }

    /// `acc + chal[role]·c`. Constants 0/1/(-1) avoid the Montgomery multiply:
    /// `c==0` drops the term, `c==1` adds the challenge, `c==-1` subtracts it.
    fn fma_const(&mut self, acc: String, role: u32, c: u32) -> String {
        if c == 0 {
            return acc;
        }
        let next = self.fresh();
        if c == 1 {
            self.line(format!("E_ADD_PERM({next}, {role}, {acc})")); // acc + chal[role]
        } else if c == NEG_ONE {
            self.line(format!("E_SUB_PERM({next}, {role}, {acc})")); // acc - chal[role]
        } else {
            self.line(format!("E_FMA_PERMC({next}, {role}, {c}, {acc})"));
        }
        next
    }

    /// Memory-tuple base-column load (shares the column-keyed CSE with gates).
    fn ensure_mem_load(&mut self, off: usize) -> String {
        self.col_load('m', "LOAD_MEM", off)
    }

    // -- gates --------------------------------------------------------------

    fn emit_gate(&mut self, layer: &CodegenLayer, gate: &CodegenGate) {
        match &gate.kind {
            GateKind::CopyInBaseField { input } | GateKind::CopyInExtensionField { input } => {
                // No-op: the output is a host-side view alias of the input.
                let out_addr = gate.dst[0].addr;
                let in_addr = self.addr_of(layer, *input);
                self.copy_aliases.push(CopyAlias {
                    output: out_addr,
                    input: in_addr,
                });
            }
            GateKind::InitialGrandProductFromCaches { input }
            | GateKind::TrivialProduct { input } => {
                let a = self.operand(layer, input[0]);
                let b = self.operand(layer, input[1]);
                let g = format!("g{}", gate.dst[0].node.0);
                self.line(format!("PRODUCT({g}, {a}, {b})"));
                self.store_inner(layer, gate, 0, &g);
            }
            GateKind::LookupPairFromMaterializedBaseInputs { input } => {
                let b = self.operand(layer, input[0]);
                let d = self.operand(layer, input[1]);
                let (num, den) = self.lookup_dsts(gate);
                self.line(format!("LOOKUP_BASE_PAIR({num}, {den}, {b}, {d})"));
                self.store_inner(layer, gate, 0, &num);
                self.store_inner(layer, gate, 1, &den);
            }
            GateKind::LookupFromMaterializedBaseInputWithSetup { input, setup } => {
                let b = self.operand(layer, *input);
                let c = self.operand(layer, setup[0]);
                let d = self.operand(layer, setup[1]);
                let (num, den) = self.lookup_dsts(gate);
                self.line(format!(
                    "LOOKUP_BASE_MINUS_MULT({num}, {den}, {b}, {c}, {d})"
                ));
                self.store_inner(layer, gate, 0, &num);
                self.store_inner(layer, gate, 1, &den);
            }
            GateKind::LookupWithCachedDensAndSetup { input, setup } => {
                let a = self.operand(layer, input[0]);
                let b = self.operand(layer, input[1]);
                let c = self.operand(layer, setup[0]);
                let d = self.operand(layer, setup[1]);
                let (num, den) = self.lookup_dsts(gate);
                self.line(format!(
                    "LOOKUP_CACHED_DENS({num}, {den}, {a}, {b}, {c}, {d})"
                ));
                self.store_inner(layer, gate, 0, &num);
                self.store_inner(layer, gate, 1, &den);
            }
            // Ext twin of LookupPairFromMaterializedBaseInputs: both inputs are
            // already-materialized ext vector tuples (VectorizedLookup caches).
            GateKind::LookupPairFromMaterializedVectorInputs { input } => {
                let a = self.operand(layer, input[0]);
                let b = self.operand(layer, input[1]);
                let (num, den) = self.lookup_dsts(gate);
                self.line(format!("LOOKUP_EXT_PAIR({num}, {den}, {a}, {b})"));
                self.store_inner(layer, gate, 0, &num);
                self.store_inner(layer, gate, 1, &den);
            }
            // Ext twin of LookupFromMaterializedBaseInputWithSetup: input is an
            // ext vector tuple, setup is (base multiplicity, ext denominator).
            GateKind::LookupFromMaterializedVectorInputWithSetup { input, setup } => {
                let b = self.operand(layer, *input);
                let c = self.operand(layer, setup[0]);
                let d = self.operand(layer, setup[1]);
                let (num, den) = self.lookup_dsts(gate);
                self.line(format!(
                    "LOOKUP_EXT_MINUS_MULT({num}, {den}, {b}, {c}, {d})"
                ));
                self.store_inner(layer, gate, 0, &num);
                self.store_inner(layer, gate, 1, &den);
            }
            // Materialize a vector lookup tuple (alpha-folded columns) as an ext
            // inner output — same folding as the VectorizedLookup cache path.
            GateKind::MaterializedVectorLookupInput { input } => {
                let v = self.emit_vectorized_lookup(layer, &input.columns, input.lookup_set_index);
                self.store_inner(layer, gate, 0, &v);
            }
            // No forward output: the constraint is checked-zero, nothing emitted.
            GateKind::EnforceSingleMaxQuadraticConstraint { .. }
            | GateKind::EnforceConstraintsMaxQuadratic { .. } => {}
            other => panic!(
                "forward codegen: gate kind {:?} not handled (layer-0 subset)",
                std::mem::discriminant(other)
            ),
        }
    }

    /// The address an operand node reads from (for recording copy aliases).
    fn addr_of(&self, layer: &CodegenLayer, id: NodeId) -> GKRAddress {
        match &layer.arena.nodes[id.0 as usize] {
            ExprNode::Place { addr, .. } => *addr,
            other => panic!("copy input node {} is not a Place: {:?}", id.0, other),
        }
    }

    fn lookup_dsts(&self, gate: &CodegenGate) -> (String, String) {
        (
            format!("g{}", gate.dst[0].node.0),
            format!("g{}", gate.dst[1].node.0),
        )
    }

    fn store_inner(&mut self, layer: &CodegenLayer, gate: &CodegenGate, slot: usize, var: &str) {
        let addr = gate.dst[slot].addr;
        assert!(
            matches!(addr, GKRAddress::InnerLayer { .. }),
            "gate output addr not InnerLayer: {addr:?}"
        );
        // Store at the layout's dense `poly_idx` column (not the raw offset) so
        // the kernel writes directly into the prover's consolidated inner-output
        // backing.
        let poly_idx = self.poly_idx_of(addr);
        // The output domain is the producing GateOutput node's domain.
        let dom = match &layer.arena.nodes[gate.dst[slot].node.0 as usize] {
            ExprNode::GateOutput { domain, .. } => *domain,
            other => panic!(
                "gate dst node {} not a GateOutput: {:?}",
                gate.dst[slot].node.0, other
            ),
        };
        match dom {
            Domain::Ext => self.line(format!("STORE_INNER_EXT({poly_idx}, {var})")),
            Domain::Base => self.line(format!("STORE_INNER_BASE({poly_idx}, {var})")),
        }
    }

    fn finish(self) -> EmittedLayer {
        EmittedLayer {
            cuh: self.out,
            copy_aliases: self.copy_aliases,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::{CodegenCircuit, GKRCircuitArtifact};

    fn load_add_sub() -> CodegenCircuit {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../cs/compiled_circuits/add_sub_lui_auipc_mop_codegen_ir_gkr.json"
        );
        let json = std::fs::read_to_string(path).unwrap_or_else(|e| {
            panic!("read {path}: {e}\n(run: cargo test -p cs codegen_ir::tests::generate_add_sub_codegen_ir_json -- --ignored)")
        });
        serde_json::from_str(&json).expect("deserialize CodegenCircuit")
    }

    /// The compiled artifact the codegen IR was lowered from. Needed to build
    /// the `GpuGKRStorageLayout` that resolves each output's `poly_idx`.
    fn load_add_sub_layout() -> GpuGKRStorageLayout {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json"
        );
        let json = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
        let artifact: GKRCircuitArtifact<F> =
            serde_json::from_str(&json).expect("deserialize GKRCircuitArtifact");
        GpuGKRStorageLayout::from_artifact(&artifact)
    }

    fn load_circuit(codegen_ir_path: &str) -> CodegenCircuit {
        let json = std::fs::read_to_string(codegen_ir_path)
            .unwrap_or_else(|e| panic!("read {codegen_ir_path}: {e}"));
        serde_json::from_str(&json).expect("deserialize CodegenCircuit")
    }

    fn load_layout(layout_path: &str) -> GpuGKRStorageLayout {
        let json = std::fs::read_to_string(layout_path)
            .unwrap_or_else(|e| panic!("read {layout_path}: {e}"));
        let artifact: GKRCircuitArtifact<F> =
            serde_json::from_str(&json).expect("deserialize GKRCircuitArtifact");
        GpuGKRStorageLayout::from_artifact(&artifact)
    }

    fn head(s: String) -> String {
        s.split([' ', '{', '(']).next().unwrap().to_string()
    }

    /// Exploratory: inventory EVERY layer of the heavier blake2 delegation
    /// circuit — gate kinds, cache kinds, and mem-tuple address/space/value forms
    /// — without emitting, so we can see the full set the generator must support
    /// before implementing. Run with:
    ///
    ///   cargo test -p gpu_gkr_fwd_generator catalog_blake2 -- --ignored --nocapture
    #[test]
    #[ignore]
    fn catalog_blake2() {
        use std::collections::BTreeMap;
        let circuit = load_circuit(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../cs/compiled_circuits/blake2_with_extended_control_codegen_ir_gkr.json"
        ));
        println!("blake2 codegen IR: {} layers", circuit.layers.len());
        let mut gate_kinds: BTreeMap<String, usize> = BTreeMap::new();
        let mut cache_kinds: BTreeMap<String, usize> = BTreeMap::new();
        let mut mt_space: BTreeMap<String, usize> = BTreeMap::new();
        let mut mt_addr: BTreeMap<String, usize> = BTreeMap::new();
        let mut mt_value: BTreeMap<String, usize> = BTreeMap::new();
        for (li, layer) in circuit.layers.iter().enumerate() {
            let mut per_gate: BTreeMap<String, usize> = BTreeMap::new();
            for gate in layer.gates.iter().chain(layer.gates_external.iter()) {
                *per_gate
                    .entry(head(format!("{:?}", gate.kind)))
                    .or_default() += 1;
            }
            let mut per_cache: BTreeMap<String, usize> = BTreeMap::new();
            for cache in &layer.caches {
                *per_cache
                    .entry(head(format!("{:?}", cache.kind)))
                    .or_default() += 1;
                if let CacheKind::MemoryTuple { descriptor } = &cache.kind {
                    let d = &descriptor.descriptor;
                    *mt_space
                        .entry(head(format!("{:?}", d.address_space)))
                        .or_default() += 1;
                    *mt_addr.entry(head(format!("{:?}", d.address))).or_default() += 1;
                    *mt_value.entry(head(format!("{:?}", d.value))).or_default() += 1;
                }
            }
            println!("layer {li}: gates={per_gate:?} caches={per_cache:?}");
            for (k, v) in per_gate {
                *gate_kinds.entry(k).or_default() += v;
            }
            for (k, v) in per_cache {
                *cache_kinds.entry(k).or_default() += v;
            }
        }
        println!("\n== TOTALS ==");
        println!("gate kinds:  {gate_kinds:?}");
        println!("cache kinds: {cache_kinds:?}");
        println!("mem-tuple address_space: {mt_space:?}");
        println!("mem-tuple address:       {mt_addr:?}");
        println!("mem-tuple value:         {mt_value:?}");
    }

    /// Emit blake2 layer 0 (after delegation + vector-lookup support). Dumps the
    /// `.cuh` to /tmp for inspection / compilation. Run with:
    ///
    ///   cargo test -p gpu_gkr_fwd_generator emits_blake2_layer0 -- --ignored --nocapture
    #[test]
    #[ignore]
    fn emits_blake2_layer0() {
        let circuit = load_circuit(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../cs/compiled_circuits/blake2_with_extended_control_codegen_ir_gkr.json"
        ));
        let layout = load_layout(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json"
        ));
        let e = emit_layer_forward(&circuit.layers[0], &circuit.globals, 0, &layout);
        let header = "// GENERATED by the `gpu_gkr_fwd_generator` crate\n\
            // (emit_layer_forward, circuit `blake2_with_extended_control`, layer 0). Do not edit.\n\
            //\n\
            // Pure macro-DSL body: one `fwd_layer_0` device function. All field ops,\n\
            // challenge constants, proxy bindings, and the kernel entry are provided by the\n\
            // enclosing `gkr_forward_generation.cuh` header + the per-circuit wrapper .cu.\n\
            // Include it inside the `airbender::prover::gkr::forward::generation` namespace.\n\n";
        let out_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../gpu/circuit_prover/native/prover/gkr/forward/generated/blake2_with_extended_control_layer0.cuh"
        );
        std::fs::write(out_path, format!("{header}{}", e.cuh)).expect("write generated .cuh");
        std::fs::write("/tmp/blake2_layer0.cuh", &e.cuh).ok();
        println!("wrote {out_path}");
        println!(
            "blake2 layer 0: {} bytes, {} copy aliases, {} lines",
            e.cuh.len(),
            e.copy_aliases.len(),
            e.cuh.lines().count()
        );
        for m in [
            "STORE_CACHE_EXT(",
            "STORE_CACHE_BASE(",
            "LOOKUP_EXT_PAIR(",
            "LOOKUP_EXT_MINUS_MULT(",
            "LOOKUP_BASE_PAIR(",
            "PRODUCT(",
            "STORE_INNER_EXT(",
        ] {
            println!("  {m} x{}", e.cuh.matches(m).count());
        }
        assert!(e.cuh.contains("FWD_FN_BEGIN(0)"));
        assert!(e.cuh.contains("FWD_FN_END"));
    }

    #[test]
    fn emits_layer0() {
        let circuit = load_add_sub();
        let layout = load_add_sub_layout();
        let e = emit_layer_forward(&circuit.layers[0], &circuit.globals, 0, &layout);
        let s = &e.cuh;
        std::fs::write("/tmp/layer0.cuh", s).ok();
        assert!(s.contains("FWD_FN_BEGIN(0)"));
        assert!(s.contains("FWD_FN_END"));
        assert_eq!(s.matches("PRODUCT(").count(), 4, "grand products");
        assert_eq!(
            s.matches("LOOKUP_BASE_PAIR(").count(),
            5,
            "base lookup pairs"
        );
        assert_eq!(
            s.matches("LOOKUP_BASE_MINUS_MULT(").count(),
            2,
            "base-with-setup"
        );
        assert_eq!(s.matches("LOOKUP_CACHED_DENS(").count(), 1, "cached-dens");
        assert_eq!(
            s.matches("STORE_CACHE_BASE(").count(),
            6,
            "single-col caches"
        );
        assert_eq!(
            s.matches("STORE_CACHE_EXT(").count(),
            10,
            "ext caches (8 memtuple+1 vec+1 setup)"
        );
        assert_eq!(e.copy_aliases.len(), 3, "3 CopyInBaseField aliases");
        // Decoder VectorizedLookup (cache 14, width 8): col_0 base→ext lift, 7
        // alpha-fma steps for cols 1..7, one predicate-select against the fill.
        assert!(
            !s.contains("DECODER_LOOKUP_TODO"),
            "decoder stub fully replaced"
        );
        assert_eq!(
            s.matches("E_FROM_BASE(").count(),
            1,
            "decoder col_0 base→ext lift"
        );
        assert_eq!(
            s.matches("E_FMA_ALPHA(").count(),
            7,
            "decoder cols 1..7 alpha-fma"
        );
        assert_eq!(
            s.matches("SELECT_DECODER_FILL(").count(),
            1,
            "decoder predicate/fill select"
        );
    }
}
