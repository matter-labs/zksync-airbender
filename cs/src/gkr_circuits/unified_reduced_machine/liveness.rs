//! Aliasing-liveness audit of the scratch-pool slots on a compiled unified artifact.
//!
//! Every relation of the compiled GKR layers is resolved down to a polynomial over base
//! columns (copies, linear relations, quadratic intermediates and lookup materializations
//! are followed back to their producers). A reader of a pool slot is a terminal relation
//! (asserted constraint, lookup input column, memory tuple) whose resolved polynomial
//! contains the slot. For every decoder row class the flags are substituted and the slot's
//! coefficient is checked for survival, with the audited slot kept a free symbol.

use super::circuit::UNIFIED_REDUCED_MACHINE_NUM_FLAGS;
use super::decoder::row_classes::unified_row_classes;
use super::decoder::UNIFIED_RD_IS_ZERO_BIT;
use crate::definitions::gkr::{LinearRelation, SingleColumnLookupRelation, VectorLookupRelation};
use crate::definitions::{GKRAddress, Variable};
use crate::gkr_compiler::{
    CompiledMaxQuadraticGKRRelation, GKRCacheRelation, GKRCircuitArtifact, GKRRelation,
    MaxQuadraticConstraintsGKRRelation, SpecialMemoryContributionRelation,
};
use crate::structured_expr::StructuredStatement;
use field::PrimeField;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Sym {
    Var(u64),
    Column(GKRAddress),
}

/// Sparse polynomial: sorted monomial -> coefficient.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Poly<F: PrimeField> {
    terms: BTreeMap<Vec<Sym>, F>,
}

impl<F: PrimeField> Poly<F> {
    fn zero() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    fn constant(c: F) -> Self {
        let mut p = Self::zero();
        p.add_term(vec![], c);
        p
    }

    fn sym(s: Sym) -> Self {
        let mut p = Self::zero();
        p.add_term(vec![s], F::ONE);
        p
    }

    fn add_term(&mut self, mut mono: Vec<Sym>, c: F) {
        if c.is_zero() {
            return;
        }
        mono.sort();
        let entry = self.terms.entry(mono).or_insert(F::ZERO);
        entry.add_assign(&c);
        if entry.is_zero() {
            self.terms.retain(|_, v| !v.is_zero());
        }
    }

    fn add_scaled(&mut self, other: &Self, scale: F) {
        for (mono, c) in other.terms.iter() {
            let mut c = *c;
            c.mul_assign(&scale);
            self.add_term(mono.clone(), c);
        }
    }

    fn mul(&self, other: &Self) -> Self {
        let mut result = Self::zero();
        for (a, ca) in self.terms.iter() {
            for (b, cb) in other.terms.iter() {
                let mut c = *ca;
                c.mul_assign(cb);
                result.add_term(a.iter().chain(b.iter()).copied().collect(), c);
            }
        }
        result
    }

    fn contains(&self, s: Sym) -> bool {
        self.terms.keys().any(|m| m.contains(&s))
    }

    fn syms(&self) -> BTreeSet<Sym> {
        self.terms.keys().flatten().copied().collect()
    }

    /// Substitute fixed values for some symbols (flags, execute, forced zeros).
    fn substitute(&self, values: &HashMap<Sym, F>) -> Self {
        let mut result = Self::zero();
        for (mono, c) in self.terms.iter() {
            let mut c = *c;
            let mut rest = Vec::with_capacity(mono.len());
            for s in mono {
                match values.get(s) {
                    Some(v) => {
                        c.mul_assign(v);
                    }
                    None => rest.push(*s),
                }
            }
            result.add_term(rest, c);
        }
        result
    }

    /// Scaled so that the coefficient of the greatest monomial is one.
    fn normalized(&self) -> Self {
        let Some((_, lead)) = self.terms.iter().next_back() else {
            return self.clone();
        };
        let mut result = Self::zero();
        result.add_scaled(self, lead.inverse().unwrap());
        result
    }
}

/// Output addresses of a relation (`GKRRelation::dump_outputs` does not cover every kind).
fn outputs_of<F: PrimeField>(rel: &GKRRelation<F>) -> Vec<GKRAddress> {
    use GKRRelation as R;
    match rel {
        R::EnforceSingleMaxQuadraticConstraint { .. }
        | R::EnforceConstraintsMaxQuadratic { .. } => {
            vec![]
        }
        R::LinearBaseFieldRelation { output, .. }
        | R::MaxQuadratic { output, .. }
        | R::CopyInBaseField { output, .. }
        | R::CopyInExtensionField { output, .. }
        | R::InitialGrandProductFromCaches { output, .. }
        | R::InitialGrandProductWithoutCaches { output, .. }
        | R::UnbalancedGrandProductWithCache { output, .. }
        | R::MaterializeGrandProductTermExpression { output, .. }
        | R::TrivialProduct { output, .. }
        | R::MaskIntoIdentityProduct { output, .. }
        | R::MaterializeSingleLookupInput { output, .. }
        | R::MaterializedVectorLookupInput { output, .. }
        | R::InitsOrTeardownsInitialPair { output, .. } => vec![*output],
        R::LookupWithCachedDensAndSetup { output, .. }
        | R::LookupWithDensAndSetupExpressions { output, .. }
        | R::LookupPairFromBaseInputs { output, .. }
        | R::LookupPairFromMaterializedBaseInputs { output, .. }
        | R::LookupFromBaseInputsWithSetup { output, .. }
        | R::LookupFromMaterializedBaseInputWithSetup { output, .. }
        | R::LookupUnbalancedPairWithMaterializedBaseInputs { output, .. }
        | R::LookupPairFromVectorInputs { output, .. }
        | R::LookupPairFromMaterializedVectorInputs { output, .. }
        | R::LookupFromVectorInputWithSetup { output, .. }
        | R::LookupFromMaterializedVectorInputWithSetup { output, .. }
        | R::LookupPairFromCachedVectorInputs { output, .. }
        | R::LookupUnbalancedPairWithVectorInputs { output, .. }
        | R::LookupUnbalancedPairWithMaterializedVectorInputs { output, .. }
        | R::AggregateLookupRationalPair { output, .. } => output.to_vec(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum ReaderKind {
    Constraint,
    LookupColumn { range_check_width: Option<u32> },
    Memory,
}

#[derive(Clone, Debug)]
struct Reader<F: PrimeField> {
    kind: ReaderKind,
    location: String,
    poly: Poly<F>,
}

enum Producer<'a, F: PrimeField> {
    Gate(&'a GKRRelation<F>),
    Cache(&'a GKRCacheRelation<F>),
}

/// Resolved value of a compiled address.
#[derive(Clone)]
enum Value<F: PrimeField> {
    Base(Poly<F>),
    /// An extension-field or tuple value built from these base polynomials.
    Composite(Vec<Poly<F>>),
    /// Setup (table) columns.
    Setup,
}

struct CompiledGraph<'a, F: PrimeField> {
    artifact: &'a GKRCircuitArtifact<F>,
    variable_at: HashMap<GKRAddress, Variable>,
    producers: HashMap<GKRAddress, Producer<'a, F>>,
    memo: RefCell<HashMap<GKRAddress, Value<F>>>,
}

impl<'a, F: PrimeField> CompiledGraph<'a, F> {
    fn new(artifact: &'a GKRCircuitArtifact<F>) -> Self {
        let variable_at = artifact
            .placement_data
            .iter()
            .map(|(v, a)| (*a, *v))
            .collect();
        let mut producers = HashMap::new();
        for layer in artifact.layers.iter() {
            for gate in layer
                .gates
                .iter()
                .chain(layer.gates_with_external_connections.iter())
            {
                let outputs = outputs_of(&gate.enforced_relation);
                for out in outputs {
                    let previous = producers.insert(out, Producer::Gate(&gate.enforced_relation));
                    assert!(previous.is_none(), "two producers of {out:?}");
                }
            }
            for (addr, cache) in layer.cached_relations.iter() {
                let previous = producers.insert(*addr, Producer::Cache(cache));
                assert!(previous.is_none(), "two producers of {addr:?}");
            }
        }
        Self {
            artifact,
            variable_at,
            producers,
            memo: RefCell::new(HashMap::new()),
        }
    }

    fn base_symbol(&self, addr: GKRAddress) -> Sym {
        match self.variable_at.get(&addr) {
            Some(v) => Sym::Var(v.0),
            None => Sym::Column(addr),
        }
    }

    fn resolve(&self, addr: GKRAddress) -> Value<F> {
        if let Some(v) = self.memo.borrow().get(&addr) {
            return v.clone();
        }
        let value = match addr {
            GKRAddress::BaseLayerWitness(_) | GKRAddress::BaseLayerMemory(_) => {
                Value::Base(Poly::sym(self.base_symbol(addr)))
            }
            GKRAddress::Setup(_) | GKRAddress::VirtualSetup(_) => Value::Setup,
            GKRAddress::ScratchSpace(i) => {
                self.resolve(self.artifact.scratch_space_mapping_rev[&i])
            }
            GKRAddress::InnerLayer { .. } | GKRAddress::Cached { .. } => {
                match self.producers.get(&addr) {
                    None => panic!("unresolved producer of {addr:?}"),
                    Some(Producer::Gate(rel)) => self.resolve_gate_output(rel),
                    Some(Producer::Cache(cache)) => match cache {
                        GKRCacheRelation::SingleColumnLookup { relation, .. } => {
                            Value::Base(self.linear(&relation.input))
                        }
                        GKRCacheRelation::VectorizedLookup(rel) => {
                            Value::Composite(self.columns(rel))
                        }
                        GKRCacheRelation::MemoryTuple(m) => Value::Composite(self.memory(m)),
                        GKRCacheRelation::VectorizedLookupSetup(_) => Value::Setup,
                    },
                }
            }
        };
        self.memo.borrow_mut().insert(addr, value.clone());
        value
    }

    fn resolve_gate_output(&self, rel: &GKRRelation<F>) -> Value<F> {
        match rel {
            GKRRelation::CopyInBaseField { input, .. }
            | GKRRelation::CopyInExtensionField { input, .. } => self.resolve(*input),
            GKRRelation::LinearBaseFieldRelation { input, .. } => Value::Base(self.linear(input)),
            GKRRelation::MaxQuadratic { input, .. } => Value::Base(self.quadratic(input)),
            GKRRelation::MaterializeSingleLookupInput { input, .. } => {
                Value::Base(self.linear(&input.input))
            }
            GKRRelation::MaterializedVectorLookupInput { input, .. } => {
                Value::Composite(self.columns(input))
            }
            other => {
                let mut inputs = BTreeSet::new();
                other.dump_inputs(&mut inputs);
                let mut polys = Vec::new();
                for i in inputs {
                    match self.resolve(i) {
                        Value::Base(p) => polys.push(p),
                        Value::Composite(ps) => polys.extend(ps),
                        Value::Setup => {}
                    }
                }
                Value::Composite(polys)
            }
        }
    }

    fn base(&self, addr: GKRAddress) -> Poly<F> {
        match self.resolve(addr) {
            Value::Base(p) => p,
            Value::Setup => Poly::sym(Sym::Column(addr)),
            Value::Composite(_) => panic!("{addr:?} is not a base-field value"),
        }
    }

    fn linear(&self, rel: &LinearRelation<F>) -> Poly<F> {
        let mut p = Poly::constant(rel.constant);
        for (c, a) in rel.linear_terms.iter() {
            p.add_scaled(&self.base(*a), *c);
        }
        p
    }

    fn columns(&self, rel: &VectorLookupRelation<F>) -> Vec<Poly<F>> {
        rel.columns.iter().map(|c| self.linear(c)).collect()
    }

    fn quadratic(&self, rel: &CompiledMaxQuadraticGKRRelation<F>) -> Poly<F> {
        let mut p = Poly::constant(rel.constant);
        for (a, terms) in rel.quadratic_terms.iter() {
            let pa = self.base(*a);
            for (c, b) in terms.iter() {
                p.add_scaled(&pa.mul(&self.base(*b)), *c);
            }
        }
        for (c, a) in rel.linear_terms.iter() {
            p.add_scaled(&self.base(*a), *c);
        }
        p
    }

    fn constraints(&self, rel: &MaxQuadraticConstraintsGKRRelation<F>) -> BTreeMap<usize, Poly<F>> {
        let mut out: BTreeMap<usize, Poly<F>> = BTreeMap::new();
        for ((a, b), coeffs) in rel.quadratic_terms.iter() {
            let ab = self.base(*a).mul(&self.base(*b));
            for (c, idx) in coeffs.iter() {
                out.entry(*idx)
                    .or_insert_with(Poly::zero)
                    .add_scaled(&ab, *c);
            }
        }
        for (a, coeffs) in rel.linear_terms.iter() {
            let pa = self.base(*a);
            for (c, idx) in coeffs.iter() {
                out.entry(*idx)
                    .or_insert_with(Poly::zero)
                    .add_scaled(&pa, *c);
            }
        }
        for (c, idx) in rel.constants.iter() {
            out.entry(*idx)
                .or_insert_with(Poly::zero)
                .add_scaled(&Poly::constant(F::ONE), *c);
        }
        out
    }

    fn memory(&self, m: &SpecialMemoryContributionRelation) -> Vec<Poly<F>> {
        m.dependencies().into_iter().map(|a| self.base(a)).collect()
    }

    /// Inputs of `rel` that resolve to base-field values not produced by a lookup
    /// materialization (those are already lookup readers).
    fn direct_base_inputs(&self, rel: &GKRRelation<F>) -> Vec<GKRAddress> {
        let mut inputs = BTreeSet::new();
        rel.dump_inputs(&mut inputs);
        inputs
            .into_iter()
            .filter(|i| {
                !matches!(
                    self.producers.get(i),
                    Some(Producer::Gate(
                        GKRRelation::MaterializeSingleLookupInput { .. }
                    )) | Some(Producer::Cache(GKRCacheRelation::SingleColumnLookup { .. }))
                )
            })
            .filter(|i| matches!(self.resolve(*i), Value::Base(_)))
            .collect()
    }

    /// Every terminal reader of the compiled graph.
    fn readers(&self) -> Vec<Reader<F>> {
        let mut readers = Vec::new();
        let mut push = |kind, location: String, poly: Poly<F>| {
            readers.push(Reader {
                kind,
                location,
                poly,
            })
        };
        let single = |rel: &SingleColumnLookupRelation<F>| self.linear(&rel.input);
        for (layer_idx, layer) in self.artifact.layers.iter().enumerate() {
            for (gate_idx, gate) in layer
                .gates
                .iter()
                .chain(layer.gates_with_external_connections.iter())
                .enumerate()
            {
                let at = |what: &str| format!("layer {layer_idx} gate {gate_idx} {what}");
                let lookup = |w: Option<u32>| ReaderKind::LookupColumn {
                    range_check_width: w,
                };
                match &gate.enforced_relation {
                    GKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => push(
                        ReaderKind::Constraint,
                        at("constraint"),
                        self.quadratic(input),
                    ),
                    GKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                        for (idx, p) in self.constraints(input) {
                            push(ReaderKind::Constraint, at(&format!("constraint #{idx}")), p);
                        }
                    }
                    GKRRelation::MaterializeSingleLookupInput {
                        input,
                        range_check_width,
                        ..
                    } => push(
                        lookup(Some(*range_check_width)),
                        at("lookup input"),
                        single(input),
                    ),
                    GKRRelation::LookupPairFromBaseInputs {
                        input,
                        range_check_width,
                        ..
                    } => {
                        for (i, rel) in input.iter().enumerate() {
                            push(
                                lookup(Some(*range_check_width)),
                                at(&format!("lookup pair input {i}")),
                                single(rel),
                            );
                        }
                    }
                    GKRRelation::LookupFromBaseInputsWithSetup {
                        input,
                        range_check_width,
                        ..
                    } => push(
                        lookup(Some(*range_check_width)),
                        at("lookup input"),
                        single(input),
                    ),
                    GKRRelation::MaterializedVectorLookupInput { input, .. }
                    | GKRRelation::LookupFromVectorInputWithSetup { input, .. }
                    | GKRRelation::LookupUnbalancedPairWithVectorInputs {
                        remainder: input, ..
                    } => {
                        for (j, p) in self.columns(input).into_iter().enumerate() {
                            push(lookup(None), at(&format!("vector lookup column {j}")), p);
                        }
                    }
                    GKRRelation::LookupPairFromVectorInputs { input, .. } => {
                        for (i, rel) in input.iter().enumerate() {
                            for (j, p) in self.columns(rel).into_iter().enumerate() {
                                push(
                                    lookup(None),
                                    at(&format!("vector lookup {i} column {j}")),
                                    p,
                                );
                            }
                        }
                    }
                    GKRRelation::LookupWithDensAndSetupExpressions {
                        input: (mask, rel), ..
                    } => {
                        push(lookup(None), at("masked lookup mask"), self.base(*mask));
                        for (j, p) in self.columns(rel).into_iter().enumerate() {
                            push(lookup(None), at(&format!("masked lookup column {j}")), p);
                        }
                    }
                    GKRRelation::InitialGrandProductWithoutCaches { input, .. } => {
                        for m in input.iter() {
                            for p in self.memory(m) {
                                push(ReaderKind::Memory, at("memory tuple"), p);
                            }
                        }
                    }
                    GKRRelation::MaterializeGrandProductTermExpression { input, .. } => {
                        for p in self.memory(input) {
                            push(ReaderKind::Memory, at("memory tuple"), p);
                        }
                    }
                    GKRRelation::LinearBaseFieldRelation { .. }
                    | GKRRelation::MaxQuadratic { .. }
                    | GKRRelation::CopyInBaseField { .. } => {}
                    GKRRelation::CopyInExtensionField { .. }
                    | GKRRelation::AggregateLookupRationalPair { .. }
                    | GKRRelation::InitsOrTeardownsInitialPair { .. } => {
                        // Pure transport of extension values or setup columns.
                        for i in self.direct_base_inputs(&gate.enforced_relation) {
                            panic!("{} consumes base value {i:?}", at("transport"));
                        }
                    }
                    GKRRelation::LookupWithCachedDensAndSetup { .. }
                    | GKRRelation::LookupPairFromMaterializedBaseInputs { .. }
                    | GKRRelation::LookupFromMaterializedBaseInputWithSetup { .. }
                    | GKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs { .. }
                    | GKRRelation::LookupPairFromMaterializedVectorInputs { .. }
                    | GKRRelation::LookupFromMaterializedVectorInputWithSetup { .. }
                    | GKRRelation::LookupPairFromCachedVectorInputs { .. }
                    | GKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs { .. } => {
                        // Lookups over already-materialized inputs; a base value that no
                        // lookup materialization produced (a bare column, a copy or an
                        // arithmetic intermediate) is a lookup input read here.
                        for i in self.direct_base_inputs(&gate.enforced_relation) {
                            push(
                                lookup(None),
                                at(&format!("materialized lookup input {i:?}")),
                                self.base(i),
                            );
                        }
                    }
                    GKRRelation::InitialGrandProductFromCaches { .. }
                    | GKRRelation::UnbalancedGrandProductWithCache { .. }
                    | GKRRelation::TrivialProduct { .. }
                    | GKRRelation::MaskIntoIdentityProduct { .. } => {
                        for i in self.direct_base_inputs(&gate.enforced_relation) {
                            push(
                                ReaderKind::Memory,
                                at(&format!("product input {i:?}")),
                                self.base(i),
                            );
                        }
                    }
                }
            }
            for (addr, cache) in layer.cached_relations.iter() {
                let at = format!("layer {layer_idx} cache {addr:?}");
                match cache {
                    GKRCacheRelation::SingleColumnLookup {
                        relation,
                        range_check_width,
                    } => push(
                        ReaderKind::LookupColumn {
                            range_check_width: Some(*range_check_width as u32),
                        },
                        at,
                        single(relation),
                    ),
                    GKRCacheRelation::VectorizedLookup(rel) => {
                        for (j, p) in self.columns(rel).into_iter().enumerate() {
                            push(
                                ReaderKind::LookupColumn {
                                    range_check_width: None,
                                },
                                format!("{at} column {j}"),
                                p,
                            );
                        }
                    }
                    GKRCacheRelation::MemoryTuple(m) => {
                        for p in self.memory(m) {
                            push(ReaderKind::Memory, at.clone(), p);
                        }
                    }
                    GKRCacheRelation::VectorizedLookupSetup(_) => {}
                }
            }
        }
        readers
    }
}

/// Polynomials of the artifact's satisfiability metadata (asserted constraints and lookup
/// expressions), with intermediate variables expanded through their `Define` statements.
/// Independent of the compiled layers; the audit requires both views to agree.
struct Metadata<'a, F: PrimeField> {
    artifact: &'a GKRCircuitArtifact<F>,
    base_vars: BTreeSet<u64>,
    defines: HashMap<u64, Poly<F>>,
}

impl<'a, F: PrimeField> Metadata<'a, F> {
    fn new(artifact: &'a GKRCircuitArtifact<F>) -> Self {
        let base_vars = artifact
            .placement_data
            .iter()
            .filter(|(_, a)| {
                matches!(
                    a,
                    GKRAddress::BaseLayerWitness(_) | GKRAddress::BaseLayerMemory(_)
                )
            })
            .map(|(v, _)| v.0)
            .collect();
        let mut defines = HashMap::new();
        for s in artifact.structured_statements.iter() {
            if let StructuredStatement::Define { dst, expr, .. } = s {
                defines.insert(dst.0, constraint_poly(&expr.to_max_quadratic_constraint()));
            }
        }
        Self {
            artifact,
            base_vars,
            defines,
        }
    }

    fn expand(&self, p: &Poly<F>) -> Poly<F> {
        let mut result = Poly::zero();
        for (mono, c) in p.terms.iter() {
            let mut term = Poly::constant(*c);
            for s in mono {
                let factor = match s {
                    Sym::Var(v) if !self.base_vars.contains(v) => {
                        let def = self.defines.get(v).unwrap_or_else(|| {
                            panic!("variable {v} is neither placed nor defined")
                        });
                        self.expand(def)
                    }
                    other => Poly::sym(*other),
                };
                term = term.mul(&factor);
            }
            result.add_scaled(&term, F::ONE);
        }
        result
    }

    fn address(&self, addr: GKRAddress) -> Poly<F> {
        let addr = match addr {
            GKRAddress::ScratchSpace(i) => self.artifact.scratch_space_mapping_rev[&i],
            other => other,
        };
        let var = self
            .artifact
            .placement_data
            .iter()
            .find(|(_, a)| **a == addr)
            .map(|(v, _)| *v);
        match var {
            Some(v) => self.expand(&Poly::sym(Sym::Var(v.0))),
            None => Poly::sym(Sym::Column(addr)),
        }
    }

    fn linear(&self, rel: &LinearRelation<F>) -> Poly<F> {
        let mut p = Poly::constant(rel.constant);
        for (c, a) in rel.linear_terms.iter() {
            p.add_scaled(&self.address(*a), *c);
        }
        p
    }

    fn polys(&self) -> Vec<(ReaderKind, Poly<F>)> {
        let mut out = Vec::new();
        for c in self.artifact.degree_2_constraints.iter() {
            let mut p = Poly::constant(c.constant_term);
            for (k, a, b) in c.quadratic_terms.iter() {
                p.add_term(vec![Sym::Var(a.0), Sym::Var(b.0)], *k);
            }
            for (k, a) in c.linear_terms.iter() {
                p.add_term(vec![Sym::Var(a.0)], *k);
            }
            out.push((ReaderKind::Constraint, self.expand(&p)));
        }
        for c in self.artifact.degree_1_constraints.iter() {
            let mut p = Poly::constant(c.constant_term);
            for (k, a) in c.linear_terms.iter() {
                p.add_term(vec![Sym::Var(a.0)], *k);
            }
            out.push((ReaderKind::Constraint, self.expand(&p)));
        }
        for rc in self.artifact.range_check_16_lookup_expressions.iter() {
            out.push((
                ReaderKind::LookupColumn {
                    range_check_width: Some(16),
                },
                self.linear(&rc.input),
            ));
        }
        for rc in self
            .artifact
            .timestamp_range_check_lookup_expressions
            .iter()
        {
            out.push((
                ReaderKind::LookupColumn {
                    range_check_width: Some(common_constants::TIMESTAMP_COLUMNS_NUM_BITS as u32),
                },
                self.linear(&rc.input),
            ));
        }
        for l in self.artifact.generic_lookups.iter() {
            for c in l.columns.iter() {
                out.push((
                    ReaderKind::LookupColumn {
                        range_check_width: None,
                    },
                    self.linear(c),
                ));
            }
        }
        out
    }
}

fn constraint_poly<F: PrimeField>(c: &crate::constraint::Constraint<F>) -> Poly<F> {
    use crate::constraint::Term;
    let mut p = Poly::zero();
    for t in c.terms.iter() {
        match t {
            Term::Constant(k) => p.add_term(vec![], *k),
            Term::Expression {
                coeff,
                inner,
                degree,
            } => p.add_term(
                inner[..*degree].iter().map(|v| Sym::Var(v.0)).collect(),
                *coeff,
            ),
        }
    }
    p
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Family {
    F1,
    F2,
    F3,
    F4,
}

fn family_of(mask: u32) -> Family {
    let dispatch = mask & !(1 << UNIFIED_RD_IS_ZERO_BIT);
    assert_eq!(dispatch.count_ones(), 1);
    match dispatch.trailing_zeros() {
        0..=9 => Family::F1,
        10..=13 => Family::F2,
        15 | 16 => Family::F3,
        17 | 18 => Family::F4,
        other => panic!("dispatch bit {other}"),
    }
}

/// One reader of an audited slot with the families on whose row classes its slot
/// coefficient survives, and whether it survives on padding.
#[derive(Clone, Debug)]
pub(super) struct SlotReader {
    pub kind: ReaderKind,
    pub location: String,
    pub names: Vec<String>,
    pub is_bare_slot: bool,
    pub live_families: BTreeSet<Family>,
    pub live_on_padding: bool,
    pub certificates: Vec<String>,
}

pub(super) struct LivenessAudit<'a, F: PrimeField> {
    artifact: &'a GKRCircuitArtifact<F>,
    readers: Vec<Reader<F>>,
    metadata: Vec<(ReaderKind, Poly<F>)>,
    execute: Sym,
    bits: [Sym; UNIFIED_REDUCED_MACHINE_NUM_FLAGS],
}

impl<'a, F: PrimeField> LivenessAudit<'a, F> {
    /// Resolves the compiled graph and checks that it agrees with the satisfiability
    /// metadata, both ways, on every polynomial that reads a scratch-pool slot.
    pub(super) fn new(artifact: &'a GKRCircuitArtifact<F>) -> Result<Self, String> {
        let graph = CompiledGraph::new(artifact);
        let readers = graph.readers();
        let named = |name: &str| -> Sym {
            let v = artifact
                .variable_names
                .iter()
                .find(|(_, n)| n.as_str() == name)
                .unwrap_or_else(|| panic!("no variable {name}"))
                .0;
            Sym::Var(v.0)
        };
        let audit = Self {
            artifact,
            readers,
            metadata: Metadata::new(artifact).polys(),
            execute: named("Execute flag for cycle"),
            bits: core::array::from_fn(|i| named(&format!("family_bit[{i}]"))),
        };

        let pool: BTreeSet<Sym> = audit.pool_slots().into_iter().map(|(_, s)| s).collect();
        let reads_pool = |p: &Poly<F>| p.syms().iter().any(|s| pool.contains(s));
        // An asserted constraint keeps its zero set under a nonzero scale, so constraints
        // compare up to scale; a lookup input does not, so lookup inputs compare exactly.
        let normalize = |kind: ReaderKind, p: &Poly<F>| match kind {
            ReaderKind::LookupColumn { .. } => (
                ReaderKind::LookupColumn {
                    range_check_width: None,
                },
                format!("{:?}", p.terms),
            ),
            k => (k, format!("{:?}", p.normalized().terms)),
        };
        let mut compiled: BTreeMap<_, usize> = BTreeMap::new();
        for r in audit.readers.iter().filter(|r| reads_pool(&r.poly)) {
            *compiled.entry(normalize(r.kind, &r.poly)).or_insert(0) += 1;
        }
        let mut metadata: BTreeMap<_, usize> = BTreeMap::new();
        for (k, p) in audit.metadata.iter().filter(|(_, p)| reads_pool(p)) {
            *metadata.entry(normalize(*k, p)).or_insert(0) += 1;
        }
        if compiled != metadata {
            let keys: BTreeSet<_> = compiled.keys().chain(metadata.keys()).collect();
            let diff: Vec<_> = keys
                .into_iter()
                .filter(|k| compiled.get(*k) != metadata.get(*k))
                .map(|k| (k, compiled.get(k).copied(), metadata.get(k).copied()))
                .collect();
            return Err(format!(
                "compiled layers and metadata disagree on pool readers \
                 (reader, compiled count, metadata count): {diff:?}"
            ));
        }
        Ok(audit)
    }

    fn name(&self, s: Sym) -> String {
        match s {
            Sym::Var(v) => self
                .artifact
                .variable_names
                .get(&Variable(v))
                .cloned()
                .unwrap_or_else(|| format!("v{v}")),
            Sym::Column(a) => format!("{a:?}"),
        }
    }

    /// (name, symbol) of every scratch-pool slot variable.
    fn pool_slots(&self) -> Vec<(String, Sym)> {
        self.artifact
            .variable_names
            .iter()
            .filter(|(_, n)| n.starts_with("shared scratch "))
            .map(|(v, n)| (n.clone(), Sym::Var(v.0)))
            .collect()
    }

    fn slot(&self, name: &str) -> Sym {
        self.pool_slots()
            .into_iter()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| panic!("no pool slot {name}"))
            .1
    }

    fn class_values(&self, execute: bool, mask: u32) -> HashMap<Sym, F> {
        let b = |x: bool| if x { F::ONE } else { F::ZERO };
        let mut values: HashMap<Sym, F> = self
            .bits
            .iter()
            .enumerate()
            .map(|(i, s)| (*s, b(mask >> i & 1 == 1)))
            .collect();
        values.insert(self.execute, b(execute));
        values
    }

    /// Variables pinned to zero on a class by constraints that do not read `slot`, with
    /// the constraint locations used.
    fn forced_zeros(
        &self,
        slot: Sym,
        mut values: HashMap<Sym, F>,
    ) -> (HashMap<Sym, F>, Vec<String>) {
        let mut certificates = Vec::new();
        loop {
            let mut progress = false;
            for r in self.readers.iter() {
                if r.kind != ReaderKind::Constraint || r.poly.contains(slot) {
                    continue;
                }
                let p = r.poly.substitute(&values);
                if p.terms.len() != 1 {
                    continue;
                }
                let (mono, _) = p.terms.iter().next().unwrap();
                if mono.len() == 1 && mono[0] != slot && !values.contains_key(&mono[0]) {
                    values.insert(mono[0], F::ZERO);
                    certificates.push(format!("{} = 0 by {}", self.name(mono[0]), r.location));
                    progress = true;
                }
            }
            if !progress {
                return (values, certificates);
            }
        }
    }

    /// Every reader of the slot named `slot_name` with its live families.
    pub(super) fn slot_readers(&self, slot_name: &str) -> Vec<SlotReader> {
        let slot = self.slot(slot_name);
        let classes: Vec<(bool, u32)> = unified_row_classes()
            .into_iter()
            .map(|m| (true, m))
            .chain([(false, 0)])
            .collect();
        let zeros: Vec<_> = classes
            .iter()
            .map(|&(e, m)| self.forced_zeros(slot, self.class_values(e, m)))
            .collect();
        let mut out = Vec::new();
        for r in self.readers.iter().filter(|r| r.poly.contains(slot)) {
            let mut reader = SlotReader {
                kind: r.kind,
                location: r.location.clone(),
                names: r.poly.syms().into_iter().map(|s| self.name(s)).collect(),
                is_bare_slot: r.poly == Poly::sym(slot),
                live_families: BTreeSet::new(),
                live_on_padding: false,
                certificates: Vec::new(),
            };
            for (&(execute, mask), (values, certs)) in classes.iter().zip(zeros.iter()) {
                if !r.poly.substitute(values).contains(slot) {
                    continue;
                }
                if execute {
                    reader.live_families.insert(family_of(mask));
                } else {
                    reader.live_on_padding = true;
                }
                reader.certificates.extend(certs.iter().cloned());
            }
            reader.certificates.sort();
            reader.certificates.dedup();
            out.push(reader);
        }
        out
    }

    /// The gate for a newly aliased slot: exactly one bare RC-16 reader, every other reader
    /// live on the row classes of one family from `owners` and never on padding, and every
    /// owner family reading the slot somewhere.
    pub(super) fn check_aliased_slot(
        &self,
        slot_name: &str,
        owners: &[Family],
    ) -> Result<Vec<SlotReader>, String> {
        let readers = self.slot_readers(slot_name);
        let slot = self.slot(slot_name);
        let range_checks = self
            .metadata
            .iter()
            .filter(|(k, p)| {
                *k == ReaderKind::LookupColumn {
                    range_check_width: Some(16),
                } && *p == Poly::sym(slot)
            })
            .count();
        if range_checks != 1 {
            return Err(format!(
                "{slot_name}: {range_checks} bare RC-16 expressions"
            ));
        }
        // The one unconditional reader allowed is the slot's RC-16: a lookup whose input is
        // exactly `1 * slot` (the metadata check above pins its table to RC-16). Every other
        // reader, bare or not, must pass the family checks.
        let is_range_reader =
            |r: &SlotReader| r.is_bare_slot && matches!(r.kind, ReaderKind::LookupColumn { .. });
        let bare_lookups = readers.iter().filter(|r| is_range_reader(r)).count();
        if bare_lookups != 1 {
            return Err(format!("{slot_name}: {bare_lookups} bare lookup readers"));
        }
        let mut seen = BTreeSet::new();
        for r in readers.iter().filter(|r| !is_range_reader(r)) {
            if r.live_on_padding {
                return Err(format!("{slot_name}: {} live on padding", r.location));
            }
            if r.live_families.len() > 1 {
                return Err(format!(
                    "{slot_name}: {} live on families {:?}",
                    r.location, r.live_families
                ));
            }
            if let Some(f) = r.live_families.iter().next() {
                if !owners.contains(f) {
                    return Err(format!(
                        "{slot_name}: {} live on {f:?}, not an owner",
                        r.location
                    ));
                }
                seen.insert(*f);
            }
        }
        for f in owners {
            if !seen.contains(f) {
                return Err(format!("{slot_name}: no {f:?} reader"));
            }
        }
        Ok(readers)
    }
}

pub(super) fn print_inventory<F: PrimeField>(label: &str, audit: &LivenessAudit<F>) {
    let mut slots = audit.pool_slots();
    slots.sort();
    for (name, _) in slots {
        for r in audit.slot_readers(&name) {
            println!(
                "{label} | {name} | {:?} | {} | live {:?}{} | reads {:?} | certificates {:?}",
                r.kind,
                r.location,
                r.live_families,
                if r.live_on_padding { " + padding" } else { "" },
                r.names,
                r.certificates
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::circuit::{
        build_unified_artifact_core, UnifiedCircuitProfile, LARGE_FIELD_UNIFIED_PROFILE,
        REGULAR_UNIFIED_PROFILE,
    };
    use super::*;
    use crate::witness_placer::graph_description::{Expression, RawExpression};
    use field::baby_bear::base::BabyBearField;
    use field::Proth120;

    const REGISTER_LOW: &str = "shared scratch var[17]";
    const REGISTER_HIGH: &str = "shared scratch var[18]";
    const PC_TMP: &str = "shared scratch var[7]";

    fn audit_artifact<F: PrimeField>(
        label: &str,
        artifact: &GKRCircuitArtifact<F>,
        profile: UnifiedCircuitProfile,
    ) {
        let audit = LivenessAudit::new(artifact).unwrap_or_else(|e| panic!("{label}: {e}"));
        print_inventory(label, &audit);
        match profile {
            UnifiedCircuitProfile::ColumnCuts => {
                use Family::*;
                for (slot, owners) in [
                    (REGISTER_LOW, &[F1, F2, F3, F4][..]),
                    (REGISTER_HIGH, &[F1, F2, F3][..]),
                    (PC_TMP, &[F2, F3][..]),
                ] {
                    audit
                        .check_aliased_slot(slot, owners)
                        .unwrap_or_else(|e| panic!("{label}: {e}"));
                }
            }
            UnifiedCircuitProfile::Baseline => {
                for slot in [REGISTER_LOW, REGISTER_HIGH, PC_TMP] {
                    for r in audit.slot_readers(slot) {
                        assert!(
                            !r.is_bare_slot && !r.live_on_padding,
                            "{label} {slot}: {r:?}"
                        );
                        assert!(
                            r.live_families.iter().all(|f| *f == Family::F3),
                            "{label} {slot}: {r:?}"
                        );
                    }
                }
            }
        }
    }

    fn audit_in_memory<F: PrimeField>(
        label: &str,
        trace_len_log2: usize,
        profile: UnifiedCircuitProfile,
    ) {
        let artifact =
            build_unified_artifact_core::<F, BabyBearField>(true, trace_len_log2, 1, profile);
        audit_artifact(&format!("{label} {profile:?}"), &artifact, profile);
    }

    #[test]
    #[ignore = "compiles four unified artifacts in memory"]
    fn aliasing_liveness_in_memory() {
        for profile in [
            UnifiedCircuitProfile::Baseline,
            UnifiedCircuitProfile::ColumnCuts,
        ] {
            audit_in_memory::<BabyBearField>("regular 2^23", 23, profile);
            audit_in_memory::<Proth120>("proth120 2^22", 22, profile);
        }
    }

    fn graph_of<F: PrimeField>(artifact: &GKRCircuitArtifact<F>) -> CompiledGraph<'_, F> {
        CompiledGraph::new(artifact)
    }

    fn column_reads<F: PrimeField>(
        graph: &CompiledGraph<'_, F>,
        column: &LinearRelation<F>,
        slot: Variable,
    ) -> bool {
        graph.linear(column).contains(Sym::Var(slot.0))
    }

    fn read_layout<F: PrimeField + serde::de::DeserializeOwned>(
        path: &str,
    ) -> GKRCircuitArtifact<F> {
        let file = std::fs::File::open(path).unwrap_or_else(|e| panic!("{path}: {e}"));
        serde_json::from_reader(std::io::BufReader::new(file)).unwrap()
    }

    #[test]
    #[ignore = "reads the committed unified layouts"]
    fn aliasing_liveness_committed_layouts() {
        let regular: GKRCircuitArtifact<BabyBearField> =
            read_layout("compiled_circuits/unified_reduced_machine_layout_gkr.json");
        audit_artifact("committed regular 2^23", &regular, REGULAR_UNIFIED_PROFILE);
        let wrap: GKRCircuitArtifact<Proth120> =
            read_layout("compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json");
        audit_artifact(
            "committed proth120 2^22",
            &wrap,
            LARGE_FIELD_UNIFIED_PROFILE,
        );
    }

    /// Test of the test: readers injected into the compiled B layers are rejected, by the
    /// compiled-vs-metadata cross-check when only the layers carry them, and by the
    /// liveness gate when the metadata carries them too.
    #[test]
    #[ignore = "compiles a unified artifact"]
    fn aliasing_liveness_checker_rejects_injected_readers() {
        use crate::definitions::gkr::LinearRelation;
        use crate::definitions::{Degree1Constraint, Degree2Constraint};
        use crate::gkr_compiler::{GateArtifacts, StructuredExpression};
        use field::Field;

        type F = BabyBearField;
        let base: GKRCircuitArtifact<F> = build_unified_artifact_core::<F, BabyBearField>(
            true,
            23,
            1,
            UnifiedCircuitProfile::ColumnCuts,
        );
        let var = |name: &str| -> Variable {
            *base
                .variable_names
                .iter()
                .find(|(_, n)| n.as_str() == name)
                .unwrap_or_else(|| panic!("no {name}"))
                .0
        };
        let addr = |v: Variable| base.placement_data[&v];
        let one = F::ONE;
        let mut two = F::ONE;
        two.add_assign(&F::ONE);
        let s17 = var(REGISTER_LOW);
        let s18 = var(REGISTER_HIGH);
        let s7 = var(PC_TMP);
        let rs1 = var("rs1 read_value[0]");
        let bit = |i: usize| var(&format!("family_bit[{i}]"));
        let fresh = |k: usize| GKRAddress::InnerLayer {
            layer: 1,
            offset: 10_000 + k,
        };
        let enforce = |input: CompiledMaxQuadraticGKRRelation<F>| GateArtifacts {
            output_layer: 1,
            enforced_relation: GKRRelation::EnforceSingleMaxQuadraticConstraint {
                input,
                expression: StructuredExpression::Constant(F::ZERO),
            },
        };
        let quad = |terms: Vec<(GKRAddress, GKRAddress)>| CompiledMaxQuadraticGKRRelation {
            quadratic_terms: terms
                .into_iter()
                .map(|(a, b)| (a, vec![(one, b)].into_boxed_slice()))
                .collect(),
            linear_terms: Box::new([]),
            constant: F::ZERO,
        };
        let d2 = |terms: Vec<(Variable, Variable)>| Degree2Constraint {
            quadratic_terms: terms.into_iter().map(|(a, b)| (one, a, b)).collect(),
            linear_terms: Box::new([]),
            constant_term: F::ZERO,
        };

        struct Control<F: PrimeField> {
            name: &'static str,
            layers: Vec<(usize, GateArtifacts<F>)>,
            caches: Vec<(usize, GKRAddress, GKRCacheRelation<F>)>,
            metadata_constraints: Vec<Degree2Constraint<F>>,
            metadata_lookups: Vec<VectorLookupRelation<F>>,
            metadata_linear: Vec<Variable>,
            metadata_rc16: Vec<LinearRelation<F>>,
            slot: &'static str,
            reason: &'static str,
        }
        let controls = vec![
            Control {
                name: "(i) ungated s7 * rs1",
                layers: vec![(0, enforce(quad(vec![(addr(s7), addr(rs1))])))],
                caches: vec![],
                metadata_constraints: vec![d2(vec![(s7, rs1)])],
                metadata_lookups: vec![],
                metadata_linear: vec![],
                metadata_rc16: vec![],
                slot: PC_TMP,
                reason: "live on padding",
            },
            Control {
                name: "(ii) (jal + shift) * s7",
                layers: vec![(
                    0,
                    enforce(quad(vec![
                        (addr(bit(10)), addr(s7)),
                        (addr(bit(15)), addr(s7)),
                    ])),
                )],
                caches: vec![],
                metadata_constraints: vec![d2(vec![(bit(10), s7), (bit(15), s7)])],
                metadata_lookups: vec![],
                metadata_linear: vec![],
                metadata_rc16: vec![],
                slot: PC_TMP,
                reason: "live on families",
            },
            Control {
                name: "(iii) lw * s7",
                layers: vec![(0, enforce(quad(vec![(addr(bit(17)), addr(s7))])))],
                caches: vec![],
                metadata_constraints: vec![d2(vec![(bit(17), s7)])],
                metadata_lookups: vec![],
                metadata_linear: vec![],
                metadata_rc16: vec![],
                slot: PC_TMP,
                reason: "not an owner",
            },
            Control {
                name: "(iv) copies and a quadratic intermediate: rs1 * s17",
                layers: vec![
                    (
                        0,
                        GateArtifacts {
                            output_layer: 1,
                            enforced_relation: GKRRelation::CopyInBaseField {
                                input: addr(s17),
                                output: fresh(0),
                            },
                        },
                    ),
                    (
                        0,
                        GateArtifacts {
                            output_layer: 1,
                            enforced_relation: GKRRelation::CopyInBaseField {
                                input: addr(rs1),
                                output: fresh(1),
                            },
                        },
                    ),
                    (
                        0,
                        GateArtifacts {
                            output_layer: 1,
                            enforced_relation: GKRRelation::MaxQuadratic {
                                input: quad(vec![(fresh(0), fresh(1))]),
                                expression: StructuredExpression::Constant(F::ZERO),
                                output: fresh(2),
                            },
                        },
                    ),
                    (
                        1,
                        enforce(CompiledMaxQuadraticGKRRelation {
                            quadratic_terms: Box::new([]),
                            linear_terms: vec![(one, fresh(2))].into_boxed_slice(),
                            constant: F::ZERO,
                        }),
                    ),
                ],
                caches: vec![],
                metadata_constraints: vec![d2(vec![(rs1, s17)])],
                metadata_lookups: vec![],
                metadata_linear: vec![],
                metadata_rc16: vec![],
                slot: REGISTER_LOW,
                reason: "live on padding",
            },
            Control {
                name: "(v) lookup column produced from a copy of s18",
                layers: vec![(
                    0,
                    GateArtifacts {
                        output_layer: 1,
                        enforced_relation: GKRRelation::CopyInBaseField {
                            input: addr(s18),
                            output: fresh(3),
                        },
                    },
                )],
                caches: vec![(
                    1,
                    GKRAddress::Cached {
                        layer: 1,
                        offset: 10_000,
                    },
                    GKRCacheRelation::VectorizedLookup(VectorLookupRelation {
                        columns: vec![LinearRelation {
                            linear_terms: vec![(one, fresh(3))].into_boxed_slice(),
                            constant: F::ZERO,
                        }]
                        .into_boxed_slice(),
                        lookup_set_index: 0,
                    }),
                )],
                metadata_constraints: vec![],
                metadata_linear: vec![],
                metadata_rc16: vec![],
                metadata_lookups: vec![VectorLookupRelation {
                    columns: vec![LinearRelation {
                        linear_terms: vec![(one, addr(s18))].into_boxed_slice(),
                        constant: F::ZERO,
                    }]
                    .into_boxed_slice(),
                    lookup_set_index: 0,
                }],
                slot: REGISTER_HIGH,
                reason: "2 bare lookup readers",
            },
            Control {
                name: "(vi) bare arithmetic constraint s7 = 0",
                layers: vec![(
                    0,
                    enforce(CompiledMaxQuadraticGKRRelation {
                        quadratic_terms: Box::new([]),
                        linear_terms: vec![(one, addr(s7))].into_boxed_slice(),
                        constant: F::ZERO,
                    }),
                )],
                caches: vec![],
                metadata_constraints: vec![],
                metadata_linear: vec![s7],
                metadata_lookups: vec![],
                metadata_rc16: vec![],
                slot: PC_TMP,
                reason: "live on padding",
            },
            Control {
                name: "(vii) scaled range-check input 2 * s7",
                layers: vec![(
                    0,
                    GateArtifacts {
                        output_layer: 1,
                        enforced_relation: GKRRelation::MaterializeSingleLookupInput {
                            input: SingleColumnLookupRelation {
                                input: LinearRelation {
                                    linear_terms: vec![(two, addr(s7))].into_boxed_slice(),
                                    constant: F::ZERO,
                                },
                                lookup_set_index: 0,
                            },
                            output: fresh(4),
                            range_check_width: 16,
                        },
                    },
                )],
                caches: vec![],
                metadata_constraints: vec![],
                metadata_linear: vec![],
                metadata_lookups: vec![],
                metadata_rc16: vec![LinearRelation {
                    linear_terms: vec![(two, addr(s7))].into_boxed_slice(),
                    constant: F::ZERO,
                }],
                slot: PC_TMP,
                reason: "live on padding",
            },
        ];

        use Family::*;
        let owners = |slot: &str| -> &'static [Family] {
            match slot {
                REGISTER_LOW => &[F1, F2, F3, F4],
                REGISTER_HIGH => &[F1, F2, F3],
                _ => &[F2, F3],
            }
        };
        for control in controls {
            let mut layers_only = base.clone();
            for (layer, gate) in control.layers.iter() {
                layers_only.layers[*layer].gates.push(gate.clone());
            }
            for (layer, key, cache) in control.caches.iter() {
                layers_only.layers[*layer]
                    .cached_relations
                    .insert(*key, cache.clone());
            }
            let err = match LivenessAudit::new(&layers_only) {
                Err(e) => e,
                Ok(_) => panic!("{}: layers-only injection not detected", control.name),
            };
            assert!(err.contains("disagree"), "{}: {err}", control.name);

            let mut both = layers_only.clone();
            both.degree_2_constraints
                .extend(control.metadata_constraints.iter().cloned());
            both.generic_lookups
                .extend(control.metadata_lookups.iter().cloned());
            both.degree_1_constraints
                .extend(control.metadata_linear.iter().map(|v| Degree1Constraint {
                    linear_terms: vec![(one, *v)].into_boxed_slice(),
                    constant_term: F::ZERO,
                }));
            both.range_check_16_lookup_expressions
                .extend(
                    control
                        .metadata_rc16
                        .iter()
                        .map(|input| SingleColumnLookupRelation {
                            input: input.clone(),
                            lookup_set_index: 0,
                        }),
                );
            let audit = LivenessAudit::new(&both)
                .unwrap_or_else(|e| panic!("{}: cross-check: {e}", control.name));
            let err = audit
                .check_aliased_slot(control.slot, owners(control.slot))
                .expect_err(control.name);
            assert!(err.contains(control.reason), "{}: {err}", control.name);
            println!("{}: rejected: {err}", control.name);
        }

        // (viii) A gated lookup column scaled by 2 in the compiled layers only (here the
        // F2 jump-cleanup input `f * s7`) must break the exact correspondence.
        let mut scaled_lookup = base.clone();
        let mut scaled = 0;
        for layer in scaled_lookup.layers.iter_mut() {
            for cache in layer.cached_relations.values_mut() {
                if let GKRCacheRelation::VectorizedLookup(rel) = cache {
                    for column in rel.columns.iter_mut() {
                        if scaled == 0 && column_reads(&graph_of(&base), column, s7) {
                            for (c, _) in column.linear_terms.iter_mut() {
                                c.mul_assign(&two);
                            }
                            scaled += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(scaled, 1);
        let err = LivenessAudit::new(&scaled_lookup)
            .err()
            .expect("(viii) compiled-only scaled lookup input not detected");
        assert!(err.contains("disagree"), "(viii): {err}");
        println!("(viii) compiled-only scaled gated lookup input: rejected: {err}");

        // (ix) The honest RC-16 of s7 replaced by 2 * s7 in both views must fail the exact
        // common-range check.
        let mut scaled_rc = base.clone();
        let s7_addr = addr(s7);
        let mut replaced = 0;
        for layer in scaled_rc.layers.iter_mut() {
            for gate in layer.gates.iter_mut() {
                let inputs: Vec<&mut GKRAddress> = match &mut gate.enforced_relation {
                    GKRRelation::LookupPairFromMaterializedBaseInputs { input, .. } => {
                        input.iter_mut().collect()
                    }
                    GKRRelation::LookupFromMaterializedBaseInputWithSetup { input, .. } => {
                        vec![input]
                    }
                    GKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                        remainder,
                        ..
                    } => vec![remainder],
                    _ => vec![],
                };
                for i in inputs {
                    if *i == s7_addr {
                        *i = fresh(5);
                        replaced += 1;
                    }
                }
            }
        }
        assert_eq!(
            replaced, 1,
            "the s7 RC-16 is a direct base-column lookup input"
        );
        scaled_rc.layers[0].gates.push(GateArtifacts {
            output_layer: 1,
            enforced_relation: GKRRelation::MaterializeSingleLookupInput {
                input: SingleColumnLookupRelation {
                    input: LinearRelation {
                        linear_terms: vec![(two, s7_addr)].into_boxed_slice(),
                        constant: F::ZERO,
                    },
                    lookup_set_index: 0,
                },
                output: fresh(5),
                range_check_width: 16,
            },
        });
        let mut rc_replaced = 0;
        for rc in scaled_rc.range_check_16_lookup_expressions.iter_mut() {
            if rc.input.linear_terms.iter().any(|(_, a)| *a == s7_addr) {
                rc.input.linear_terms = vec![(two, s7_addr)].into_boxed_slice();
                rc_replaced += 1;
            }
        }
        assert_eq!(rc_replaced, 1);
        let audit = LivenessAudit::new(&scaled_rc).expect("(ix) both views agree");
        let err = audit
            .check_aliased_slot(PC_TMP, owners(PC_TMP))
            .expect_err("(ix) scaled RC-16 accepted");
        assert!(err.contains("0 bare RC-16 expressions"), "(ix): {err}");
        println!("(ix) consistently scaled RC-16 input: rejected: {err}");
    }

    /// The decoder tuple the trace-level oracle (`check_decoder_lookup` in the prover
    /// tests) rebuilds from `memory_layout.decoder_input` and `machine_state` is exactly
    /// the compiled masked decoder lookup: mask = execute, columns = (pc[0], pc[1], rs1,
    /// rs2, rd, imm[0], imm[1], funct3, Σ 2^i · family_bit[i], decoder table id).
    #[test]
    #[ignore = "compiles unified artifacts"]
    fn decoder_lookup_oracle_matches_compiled_relation() {
        fn check<F: PrimeField>(label: &str, artifact: &GKRCircuitArtifact<F>) {
            let graph = CompiledGraph::new(artifact);
            let machine = artifact.memory_layout.machine_state.unwrap();
            let decoder = artifact.memory_layout.decoder_input.as_ref().unwrap();
            let mem = |i: usize| graph.base(GKRAddress::BaseLayerMemory(i));
            let side = |i: usize| {
                if decoder.decoder_witness_is_in_memory {
                    graph.base(GKRAddress::BaseLayerMemory(i))
                } else {
                    graph.base(GKRAddress::BaseLayerWitness(i))
                }
            };
            let mut mask = Poly::zero();
            let mut power = F::ONE;
            for bit in decoder.circuit_family_mask_bits.iter() {
                mask.add_scaled(&graph.base(*bit), power);
                power.double();
            }
            let expected = vec![
                mem(machine.initial_state.pc[0]),
                mem(machine.initial_state.pc[1]),
                mem(decoder.rs1_index),
                graph.base(decoder.rs2_index),
                graph.base(decoder.rd_index),
                side(decoder.imm[0]),
                side(decoder.imm[1]),
                side(decoder.funct3.unwrap()),
                mask,
                Poly::constant(F::from_u32_unchecked(
                    crate::tables::TableType::Decoder as u32,
                )),
            ];
            let execute = mem(machine.execute);

            let mut masked = Vec::new();
            for layer in artifact.layers.iter() {
                for gate in layer
                    .gates
                    .iter()
                    .chain(layer.gates_with_external_connections.iter())
                {
                    match &gate.enforced_relation {
                        GKRRelation::LookupWithCachedDensAndSetup {
                            input: [m, cached], ..
                        } => {
                            if let Some(Producer::Cache(GKRCacheRelation::VectorizedLookup(rel))) =
                                graph.producers.get(cached)
                            {
                                masked.push((graph.base(*m), graph.columns(rel)));
                            }
                        }
                        GKRRelation::LookupWithDensAndSetupExpressions {
                            input: (m, rel), ..
                        } => masked.push((graph.base(*m), graph.columns(rel))),
                        _ => {}
                    }
                }
            }
            let decoder_lookups: Vec<_> = masked.iter().filter(|(m, _)| *m == execute).collect();
            assert_eq!(decoder_lookups.len(), 1, "{label}: execute-masked lookups");
            let got = &decoder_lookups[0].1;
            assert_eq!(got.len(), expected.len(), "{label}: decoder tuple width");
            for (i, (g, e)) in got.iter().zip(expected.iter()).enumerate() {
                assert_eq!(g, e, "{label}: decoder tuple column {i}");
            }
        }

        for profile in [
            UnifiedCircuitProfile::Baseline,
            UnifiedCircuitProfile::ColumnCuts,
        ] {
            for use_caches in [true, false] {
                let regular = build_unified_artifact_core::<BabyBearField, BabyBearField>(
                    use_caches, 23, 1, profile,
                );
                check(
                    &format!("regular {profile:?} caches={use_caches}"),
                    &regular,
                );
            }
            let wrap = build_unified_artifact_core::<Proth120, BabyBearField>(true, 22, 1, profile);
            check(&format!("proth120 {profile:?}"), &wrap);
        }
    }

    fn slot_write_types<F: PrimeField>(
        ssa: &[Vec<RawExpression<F>>],
        slot: Variable,
    ) -> Vec<&'static str> {
        ssa.iter()
            .flatten()
            .filter_map(|e| match e {
                RawExpression::WriteVariable {
                    into_variable,
                    source_subexpr,
                    ..
                } if *into_variable == slot => Some(match source_subexpr {
                    Expression::Bool(_) => "bool",
                    Expression::Field(_) => "field",
                    Expression::U8(_) => "u8",
                    Expression::U16(_) => "u16",
                    Expression::U32(_) => "u32",
                }),
                _ => None,
            })
            .collect()
    }

    /// A masked-off write in the generated witness function reads the slot back at the
    /// writer's own width, so a u8 or bool writer of an aliased slot truncates the u16
    /// value another family left there.
    fn check_slot_write_widths<F: PrimeField>(
        label: &str,
        artifact: &GKRCircuitArtifact<F>,
        ssa: &[Vec<RawExpression<F>>],
        profile: UnifiedCircuitProfile,
    ) {
        for slot in [REGISTER_LOW, REGISTER_HIGH, PC_TMP] {
            let named: Vec<Variable> = artifact
                .variable_names
                .iter()
                .filter(|(_, n)| n.as_str() == slot)
                .map(|(v, _)| *v)
                .collect();
            assert_eq!(named.len(), 1, "{label}: {slot}");
            let types = slot_write_types(ssa, named[0]);
            println!("{label} {slot}: writers {types:?}");
            let narrow = types.iter().any(|t| matches!(*t, "u8" | "bool"));
            match profile {
                UnifiedCircuitProfile::ColumnCuts => {
                    assert!(types.len() >= 2, "{label} {slot}: not aliased {types:?}");
                    assert!(!narrow, "{label} {slot}: sub-u16 writer {types:?}");
                }
                UnifiedCircuitProfile::Baseline => {
                    if slot != PC_TMP {
                        assert!(narrow, "{label} {slot}: control lost the F3 byte split");
                    }
                }
            }
        }
    }

    #[test]
    #[ignore = "dumps four unified witness graphs"]
    fn aliased_slot_writers_are_at_least_u16_in_memory() {
        use super::super::circuit::{
            unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core,
            unified_register_all_tables,
        };
        use crate::gkr_compiler::dump_ssa_witness_eval_form;

        fn check<F: PrimeField>(label: &str, trace_len_log2: usize) {
            for profile in [
                UnifiedCircuitProfile::Baseline,
                UnifiedCircuitProfile::ColumnCuts,
            ] {
                let artifact = build_unified_artifact_core::<F, BabyBearField>(
                    true,
                    trace_len_log2,
                    1,
                    profile,
                );
                let ssa =
                    dump_ssa_witness_eval_form::<F>(&|cs| unified_register_all_tables(cs), &|cs| {
                        unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core::<
                            F,
                            BabyBearField,
                            _,
                        >(cs, profile)
                    });
                check_slot_write_widths(&format!("{label} {profile:?}"), &artifact, &ssa, profile);
            }
        }
        check::<BabyBearField>("regular 2^23", 23);
        check::<Proth120>("proth120 2^22", 22);
    }

    #[test]
    #[ignore = "reads the committed unified layouts and witness graphs"]
    fn aliased_slot_writers_are_at_least_u16_committed() {
        fn read_ssa<F: PrimeField + serde::de::DeserializeOwned>(
            path: &str,
        ) -> Vec<Vec<RawExpression<F>>> {
            let file = std::fs::File::open(path).unwrap_or_else(|e| panic!("{path}: {e}"));
            serde_json::from_reader(std::io::BufReader::new(file)).unwrap()
        }
        let regular: GKRCircuitArtifact<BabyBearField> =
            read_layout("compiled_circuits/unified_reduced_machine_layout_gkr.json");
        check_slot_write_widths(
            "committed regular",
            &regular,
            &read_ssa::<BabyBearField>("compiled_circuits/unified_reduced_machine_ssa_gkr.json"),
            REGULAR_UNIFIED_PROFILE,
        );
        let wrap: GKRCircuitArtifact<Proth120> =
            read_layout("compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json");
        check_slot_write_widths(
            "committed proth120",
            &wrap,
            &read_ssa::<Proth120>(
                "compiled_circuits/unified_reduced_machine_ssa_gkr_proth120.json",
            ),
            LARGE_FIELD_UNIFIED_PROFILE,
        );
    }
}
