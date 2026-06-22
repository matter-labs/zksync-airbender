use std::collections::BTreeSet;

use super::*;
use crate::gkr::prover::sumcheck_loop::batch_evaluation::BatchedGKRDescription;
use cs::definitions::gkr::NoFieldLinearRelation;
use cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES;
use cs::gkr_compiler::{NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation};

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    pub(crate) fn analyze_terms(&self) {
        let challenge_constants = BatchedGKRTermDescriptionConstants {
            external_challenges: GKRExternalChallenges {
                permutation_argument_linearization_challenges: [E::ONE;
                    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES],
                permutation_argument_additive_part: E::ONE,
                _marker: core::marker::PhantomData,
            },
            lookup_challenges_additive_part: E::ONE,
            lookup_challenges_multiplicative_part: E::ONE,
            _marker: core::marker::PhantomData,
        };
        let batched_description = self.make_batched_description(&challenge_constants, self.layer);

        #[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
        struct Occurances {
            quad_terms_with_base: BTreeSet<GKRAddress>,
            quad_terms_with_ext: BTreeSet<GKRAddress>,
            linear_terms: bool,
        }

        let mut occurances_of_base = BTreeMap::<_, Occurances>::new();
        let mut occurances_of_ext = BTreeMap::<_, Occurances>::new();
        for (a, other) in batched_description.quadratic_part_base_by_base.iter() {
            let e = occurances_of_base.entry(*a).or_default();
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                e.quad_terms_with_base.insert(*b);
            }
            // symmetric
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                let e = occurances_of_base.entry(*b).or_default();
                e.quad_terms_with_base.insert(*a);
            }
        }
        for (a, other) in batched_description.quadratic_part_base_by_ext.iter() {
            let e = occurances_of_base.entry(*a).or_default();
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                e.quad_terms_with_ext.insert(*b);
            }
            // symmetric
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                let e = occurances_of_ext.entry(*b).or_default();
                e.quad_terms_with_base.insert(*a);
            }
        }
        for (a, other) in batched_description.quadratic_part_base_by_ext.iter() {
            let e = occurances_of_ext.entry(*a).or_default();
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                e.quad_terms_with_ext.insert(*b);
            }
            // symmetric
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                let e = occurances_of_ext.entry(*b).or_default();
                e.quad_terms_with_ext.insert(*a);
            }
        }
        for (a, _) in batched_description.linear_part_base_by_everything.iter() {
            let e = occurances_of_base.entry(*a).or_default();
            e.linear_terms = true;
        }
        for (a, _) in batched_description.linear_part_ext_by_everything.iter() {
            let e = occurances_of_ext.entry(*a).or_default();
            e.linear_terms = true;
        }

        for (a, o) in occurances_of_base.iter() {
            let with_base = o.quad_terms_with_base.len();
            let with_ext = o.quad_terms_with_ext.len();
            let in_linear = o.linear_terms as usize;
            println!("Base variable {:?} happens in {} quad terms with base, {} quad terms with ext and {} linear terms", a, with_base, with_ext, in_linear);
        }

        for (a, o) in occurances_of_ext.iter() {
            let with_base = o.quad_terms_with_base.len();
            let with_ext = o.quad_terms_with_ext.len();
            let in_linear = o.linear_terms as usize;
            println!("Ext variable {:?} happens in {} quad terms with base, {} quad terms with ext and {} linear terms", a, with_base, with_ext, in_linear);
        }
    }

    /// Build the interaction graph induced by the `quadratic_part_base_by_base` terms of the
    /// batched description, and partition it.
    ///
    /// Each quadratic term contributes an undirected edge between the two [`GKRAddress`]es it
    /// multiplies: if `a` is a key in the (conceptual) map and `b` appears as one of the entries of
    /// its value `Vec<(GKRAddress, E)>`, then the graph has an edge `a -- b`.
    pub(crate) fn partition_quadratic_graph(&self, target_cluster_size: usize) -> GraphPartitioning<E> {
        let challenge_constants = BatchedGKRTermDescriptionConstants {
            external_challenges: GKRExternalChallenges {
                permutation_argument_linearization_challenges: [E::ONE;
                    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES],
                permutation_argument_additive_part: E::ONE,
                _marker: core::marker::PhantomData,
            },
            lookup_challenges_additive_part: E::ONE,
            lookup_challenges_multiplicative_part: E::ONE,
            _marker: core::marker::PhantomData,
        };
        let batched_description = self.make_batched_description(&challenge_constants, self.layer);

        let mut graph = AddressGraph::new();
        graph.add_quadratic_part(batched_description.quadratic_part_base_by_base.iter());
        graph.add_quadratic_part(batched_description.quadratic_part_base_by_ext.iter());
        graph.add_quadratic_part(batched_description.quadratic_part_ext_by_ext.iter());

        println!(
            "merged quadratic graph (base_by_base + base_by_ext + ext_by_ext): {} vertices, {} edges",
            graph.num_vertices(),
            graph.num_edges()
        );

        let clusters = graph.greedy_clusters(target_cluster_size);
        let partitioning = graph.build_partitioning(&clusters);

        // Reporting.
        let isolated_pairs = clusters
            .iter()
            .filter(|c| c.kind == ClusterKind::IsolatedPair)
            .count();
        let singletons = clusters
            .iter()
            .filter(|c| c.kind == ClusterKind::Singleton)
            .count();
        let clustered = clusters
            .iter()
            .filter(|c| c.kind == ClusterKind::Clustered)
            .count();
        // An address that lands in more than one cluster is shared (overlap / separator variable).
        let shared = partitioning
            .address_to_partitions
            .values()
            .filter(|parts| parts.len() > 1)
            .count();
        let overlap_incidences: usize = partitioning
            .address_to_partitions
            .values()
            .map(|parts| parts.len() - 1)
            .sum();
        println!(
            "Two-phase partition (target cluster size {}): {} cluster(s) total = \
             {} isolated pair(s) + {} singleton(s) + {} grown cluster(s).",
            target_cluster_size,
            clusters.len(),
            isolated_pairs,
            singletons,
            clustered,
        );
        println!(
            "  Phase 2 overlap: {} shared address(es), {} total overlap incidence(s).",
            shared, overlap_incidences,
        );
        let sizes: Vec<usize> = clusters.iter().map(|c| c.vertices.len()).collect();
        println!("  cluster sizes = {:?}", sizes);

        partitioning
    }

    /// Treat the batched description as one abstract quadratic form
    ///
    /// ```text
    ///   acc = const + Σ c_i · x_i        (linear terms)
    ///             + Σ c_ij · x_i · x_j   (quadratic terms)
    /// ```
    ///
    /// and emit a straight-line evaluation program that uses at most `scratch_space` slots for live
    /// values, trying to minimise how many times an input has to be (re-)read from memory.
    ///
    /// Cost model: every term must have all of its operands resident in scratch at the moment it is
    /// evaluated, and the running accumulator is itself an intermediate that permanently occupies one
    /// scratch slot — so the input cache has `scratch_space - 1` slots. Loading an input that was
    /// loaded before and since evicted is a *re-read*, which is exactly what we minimise.
    ///
    /// The optimiser is a simple greedy scheduler: it repeatedly runs whichever term needs the fewest
    /// new loads (preferring terms whose operands are already resident, then those whose new operands
    /// are reused the most), and when it must evict it drops the resident input with the fewest
    /// remaining uses (a Belady-style "evict the one needed furthest in the future" proxy).
    pub(crate) fn optimize_quadratic_evaluation(
        &self,
        scratch_space: usize,
        scheduler: Scheduler,
    ) -> EvaluationPlan<E> {
        assert!(
            scratch_space >= 3,
            "need >=1 slot for the accumulator and >=2 for a quadratic term's operands"
        );
        let (addresses, terms) = self.flatten_quadratic_form();
        schedule(&addresses, &terms, scratch_space, scheduler)
    }

    /// Same scratch-space model as [`optimize_quadratic_evaluation`], but evaluate the form one
    /// *independent partition at a time*.
    ///
    /// The quadratic form's variables split into connected components: two variables are linked iff
    /// they share a quadratic term, and a variable that only appears in linear terms is its own
    /// component. Components share no variables, so they are independent subexpressions — evaluating
    /// one never needs a value from another, and the scratch is wiped between them.
    ///
    /// Consequences:
    /// * Any component whose variable count fits in the input cache (`scratch_space - 1`) is a
    ///   **zero-re-read subexpression**: load each member once, run all its terms, done.
    /// * Only components larger than the cache can incur re-reads, and those are confined to the
    ///   component — they can never thrash against unrelated variables.
    ///
    /// We emit the fitting (free) partitions first, then greedily schedule the oversized ones with
    /// the same stable, deterministic greedy as before.
    pub(crate) fn optimize_quadratic_evaluation_partitioned(
        &self,
        scratch_space: usize,
        scheduler: Scheduler,
    ) -> PartitionedPlan<E> {
        assert!(
            scratch_space >= 3,
            "need >=1 slot for the accumulator and >=2 for a quadratic term's operands"
        );
        let input_capacity = scratch_space - 1;
        let (addresses, terms) = self.flatten_quadratic_form();
        let n_vars = addresses.len();

        // Union variables that share a quadratic term -> connected components.
        let mut parent: Vec<usize> = (0..n_vars).collect();
        fn find(parent: &mut [usize], mut x: usize) -> usize {
            while parent[x] != x {
                parent[x] = parent[parent[x]];
                x = parent[x];
            }
            x
        }
        for t in terms.iter() {
            if let Some(b) = t.b {
                let (ra, rb) = (find(&mut parent, t.a), find(&mut parent, b));
                if ra != rb {
                    parent[ra] = rb;
                }
            }
        }

        // Collect each component's member variables and the terms assigned to it.
        let mut members_of: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        let mut terms_of: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for v in 0..n_vars {
            let r = find(&mut parent, v);
            members_of.entry(r).or_default().push(v);
        }
        for (i, t) in terms.iter().enumerate() {
            let r = find(&mut parent, t.a);
            terms_of.entry(r).or_default().push(i);
        }

        // Schedule each component independently with fresh scratch, then order the results so the
        // free (fitting) partitions come first.
        let mut partition_plans: Vec<PartitionPlan<E>> = Vec::new();
        for (root, members) in members_of.iter() {
            // Local dense re-indexing for this partition.
            let local_addresses: Vec<GKRAddress> = members.iter().map(|&v| addresses[v]).collect();
            let local_index: BTreeMap<usize, usize> = members
                .iter()
                .enumerate()
                .map(|(local, &global)| (global, local))
                .collect();
            let local_terms: Vec<AbstractTerm<E>> = terms_of
                .get(root)
                .map(|idxs| idxs.as_slice())
                .unwrap_or(&[])
                .iter()
                .map(|&i| {
                    let t = &terms[i];
                    AbstractTerm {
                        a: local_index[&t.a],
                        b: t.b.map(|b| local_index[&b]),
                        coeff: t.coeff,
                    }
                })
                .collect();

            let plan = schedule(&local_addresses, &local_terms, scratch_space, scheduler);
            partition_plans.push(PartitionPlan {
                members: local_addresses,
                fits: members.len() <= input_capacity,
                total_reads: plan.total_reads,
                re_reads: plan.re_reads,
                steps: plan.steps,
            });
        }

        // Stable order: free partitions first (largest first within each group for readability).
        partition_plans.sort_by_key(|p| (!p.fits, std::cmp::Reverse(p.members.len())));

        let distinct_inputs = n_vars;
        let naive_reads: usize = partition_plans
            .iter()
            .flat_map(|p| p.steps.iter())
            .filter(|s| matches!(s, EvalStep::MulAdd { .. } | EvalStep::LinearAdd { .. }))
            .map(|s| match s {
                EvalStep::MulAdd { .. } => 2,
                _ => 1,
            })
            .sum();
        let total_reads: usize = partition_plans.iter().map(|p| p.total_reads).sum();
        let re_reads: usize = partition_plans.iter().map(|p| p.re_reads).sum();
        let fitting_partitions = partition_plans.iter().filter(|p| p.fits).count();
        let oversized_partitions = partition_plans.len() - fitting_partitions;

        PartitionedPlan {
            scratch_space,
            partitions: partition_plans,
            distinct_inputs,
            naive_reads,
            total_reads,
            re_reads,
            fitting_partitions,
            oversized_partitions,
        }
    }

    /// Flatten the batched description into a dense variable set and a flat list of abstract terms.
    fn flatten_quadratic_form(&self) -> (Vec<GKRAddress>, Vec<AbstractTerm<E>>) {
        let challenge_constants = BatchedGKRTermDescriptionConstants {
            external_challenges: GKRExternalChallenges {
                permutation_argument_linearization_challenges: [E::ONE;
                    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES],
                permutation_argument_additive_part: E::ONE,
                _marker: core::marker::PhantomData,
            },
            lookup_challenges_additive_part: E::ONE,
            lookup_challenges_multiplicative_part: E::ONE,
            _marker: core::marker::PhantomData,
        };
        let description = self.make_batched_description(&challenge_constants, self.layer);

        let mut index_of: BTreeMap<GKRAddress, usize> = BTreeMap::new();
        let mut addresses: Vec<GKRAddress> = Vec::new();
        let mut intern = |addr: GKRAddress,
                          index_of: &mut BTreeMap<GKRAddress, usize>,
                          addresses: &mut Vec<GKRAddress>|
         -> usize {
            if let Some(&i) = index_of.get(&addr) {
                return i;
            }
            let i = addresses.len();
            addresses.push(addr);
            index_of.insert(addr, i);
            i
        };

        let mut terms: Vec<AbstractTerm<E>> = Vec::new();
        for part in [
            &description.quadratic_part_base_by_base,
            &description.quadratic_part_base_by_ext,
            &description.quadratic_part_ext_by_ext,
        ] {
            for (a, others) in part.iter() {
                let ai = intern(*a, &mut index_of, &mut addresses);
                for (b, coeff) in others.iter() {
                    let bi = intern(*b, &mut index_of, &mut addresses);
                    terms.push(AbstractTerm {
                        a: ai,
                        b: Some(bi),
                        coeff: *coeff,
                    });
                }
            }
        }
        for part in [
            &description.linear_part_base_by_everything,
            &description.linear_part_ext_by_everything,
        ] {
            for (a, coeff) in part.iter() {
                let ai = intern(*a, &mut index_of, &mut addresses);
                terms.push(AbstractTerm {
                    a: ai,
                    b: None,
                    coeff: *coeff,
                });
            }
        }

        (addresses, terms)
    }

    /// Compare the cost (field multiplications and additions) of evaluating this layer two ways:
    ///
    /// * **Batched** — the flattened [`BatchedGKRDescription`]. Flattening distributes the random
    ///   batching challenges into every coefficient, so a constraint `gamma * (a*b + a*c)` becomes
    ///   `(gamma*a)*b + ... ` — every monomial carries a non-trivial (random) coefficient and is a
    ///   separate product. We therefore charge one coefficient-multiply per monomial.
    /// * **Individual gates** — each gate evaluated with its native bracket structure (e.g. a max-
    ///   quadratic constraint keeps `a * (c1*b1 + c2*b2 + ...)` as one product), with the small
    ///   integer coefficients `1`/`-1` charged as free. The batching challenge is *not* distributed;
    ///   instead each gate pays it once: **one multiply per output, or one multiply if it has no
    ///   output** (a pure enforced constraint).
    ///
    /// Multiplications are reported in two kinds:
    /// * **challenge** — folding the batching challenge: the batched mode's per-monomial coefficient
    ///   multiply is modeled as the *same kind* as the gate mode's per-output fold;
    /// * **internal** — the multiplications done inside the evaluation itself (structural products
    ///   and any native integer-coefficient scaling), counted as a separate kind.
    pub(crate) fn compare_gate_vs_batched_cost(
        &self,
        layer: &GKRLayerDescription,
    ) -> CostComparison {
        let challenge_constants = BatchedGKRTermDescriptionConstants {
            external_challenges: GKRExternalChallenges {
                permutation_argument_linearization_challenges: [E::ONE;
                    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES],
                permutation_argument_additive_part: E::ONE,
                _marker: core::marker::PhantomData,
            },
            lookup_challenges_additive_part: E::ONE,
            lookup_challenges_multiplicative_part: E::ONE,
            _marker: core::marker::PhantomData,
        };
        let description = self.make_batched_description(&challenge_constants, self.layer);
        let batched = batched_form_cost(&description);

        let p = F::CHARACTERISTICS;
        let mut gate_native = EvalCost::default();
        let mut gate_native_cse = EvalCost::default();
        let mut gate_batching_mults = 0usize;
        let mut num_gates = 0usize;
        let mut unmodeled_gates = 0usize;
        // Inner linear combinations already materialized, shared across all max-quadratic gates so a
        // common sub-expression is built once and then reused.
        let mut materialized: BTreeSet<Vec<(u32, GKRAddress)>> = BTreeSet::new();
        for gate in layer
            .gates_with_external_connections
            .iter()
            .chain(layer.gates.iter())
        {
            num_gates += 1;
            let rel = &gate.enforced_relation;
            match native_gate_cost(rel, p) {
                Some(cost) => gate_native += cost,
                None => unmodeled_gates += 1,
            }
            // CSE variant: max-quadratic constraints share inner-linear-form construction.
            match rel {
                NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input }
                | NoFieldGKRRelation::MaxQuadratic { input, .. } => {
                    gate_native_cse += max_quadratic_cse_cost(input, p, &mut materialized);
                }
                other => {
                    if let Some(cost) = native_gate_cost(other, p) {
                        gate_native_cse += cost;
                    }
                }
            }
            // The batching challenge is folded in once per output (or once if there is no output).
            let outputs = num_outputs(rel);
            gate_batching_mults += if outputs > 0 { outputs } else { 1 };
        }

        CostComparison {
            batched,
            gate_native,
            gate_native_cse,
            gate_batching_mults,
            num_gates,
            unmodeled_gates,
        }
    }
}

/// Field-operation cost split into the two kinds of multiply we care about, plus additions.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct EvalCost {
    /// Multiplications of two runtime values (`var * var`, or `var * inner-sum`).
    pub(crate) product_mults: usize,
    /// Multiplications by a non-trivial constant / challenge (i.e. not `0`, `1` or `-1`).
    pub(crate) coeff_mults: usize,
    pub(crate) adds: usize,
}

impl EvalCost {
    pub(crate) fn total_mults(&self) -> usize {
        self.product_mults + self.coeff_mults
    }
}

impl core::ops::AddAssign for EvalCost {
    fn add_assign(&mut self, rhs: Self) {
        self.product_mults += rhs.product_mults;
        self.coeff_mults += rhs.coeff_mults;
        self.adds += rhs.adds;
    }
}

/// Side-by-side cost of evaluating a layer batched vs as individual gates.
#[derive(Clone, Debug)]
pub(crate) struct CostComparison {
    pub(crate) batched: EvalCost,
    pub(crate) gate_native: EvalCost,
    /// Like `gate_native`, but max-quadratic constraints share the construction of identical inner
    /// linear combinations (common subexpression elimination).
    pub(crate) gate_native_cse: EvalCost,
    /// Challenge folds: one multiply per gate output, or one per output-less gate.
    pub(crate) gate_batching_mults: usize,
    pub(crate) num_gates: usize,
    pub(crate) unmodeled_gates: usize,
}

impl CostComparison {
    /// "Challenge" multiplications: folding a random batching challenge in. In batched mode this is
    /// the per-monomial coefficient multiply; in gate mode it is the per-output (or single
    /// output-less) fold. The two are modeled as the *same kind* of multiply.
    pub(crate) fn batched_challenge_mults(&self) -> usize {
        self.batched.coeff_mults
    }
    pub(crate) fn gate_challenge_mults(&self) -> usize {
        self.gate_batching_mults
    }

    /// "Internal" multiplications done *inside* the evaluation: structural products plus any native
    /// (non-challenge) integer-coefficient scaling. A separate kind from the challenge folds.
    pub(crate) fn batched_internal_mults(&self) -> usize {
        // Batched coefficients are all challenges, so the only internal mults are the products.
        self.batched.product_mults
    }
    pub(crate) fn gate_internal_mults(&self) -> usize {
        self.gate_native.product_mults + self.gate_native.coeff_mults
    }
    /// Internal multiplications with common-subexpression elimination on the max-quadratic gates.
    pub(crate) fn gate_internal_mults_cse(&self) -> usize {
        self.gate_native_cse.product_mults + self.gate_native_cse.coeff_mults
    }
}

/// Cost of evaluating the flattened batched description. Its coefficients are products of the
/// constraints' integer coefficients with random transcript challenges, hence generically
/// non-trivial, so every stored monomial is charged one coefficient-multiply.
fn batched_form_cost<F: PrimeField, E: FieldExtension<F> + Field>(
    desc: &BatchedGKRDescription<F, E>,
) -> EvalCost {
    let mut cost = EvalCost::default();
    for part in [
        &desc.quadratic_part_base_by_base,
        &desc.quadratic_part_base_by_ext,
        &desc.quadratic_part_ext_by_ext,
    ] {
        for (_a, inner) in part.iter() {
            let k = inner.len();
            if k == 0 {
                continue;
            }
            cost.coeff_mults += k; // one random-challenge multiply per monomial
            cost.product_mults += 1; // a * (inner sum)
            cost.adds += k; // (k - 1) to build the inner sum + 1 to accumulate
        }
    }
    for part in [
        &desc.linear_part_base_by_everything,
        &desc.linear_part_ext_by_everything,
    ] {
        for _ in part.iter() {
            cost.coeff_mults += 1;
            cost.adds += 1;
        }
    }
    if !desc.constant_term.is_zero() {
        cost.adds += 1;
    }
    cost
}

/// Whether a `u32` coefficient is non-trivial (costs a multiply): anything but `0`, `1`, `p-1`.
fn u32_coeff_is_mult(coeff: u32, p: u32) -> bool {
    coeff != 0 && coeff != 1 && coeff != p - 1
}

/// Native (bracket-preserving) cost of a max-quadratic relation `Σ a*(Σ c_j b_j) + Σ c_k v_k + c`.
fn max_quadratic_native_cost(rel: &NoFieldMaxQuadraticGKRRelation, p: u32) -> EvalCost {
    let mut cost = EvalCost::default();
    for (_a, inner) in rel.quadratic_terms.iter() {
        let mut nonzero = 0usize;
        for (coeff, _b) in inner.iter() {
            if *coeff == 0 {
                continue;
            }
            nonzero += 1;
            if u32_coeff_is_mult(*coeff, p) {
                cost.coeff_mults += 1;
            }
        }
        if nonzero > 0 {
            cost.product_mults += 1; // one multiply of `a` by the bracketed inner sum
            cost.adds += nonzero; // (nonzero - 1) to sum the inner + 1 to accumulate
        }
    }
    for (coeff, _v) in rel.linear_terms.iter() {
        if *coeff == 0 {
            continue;
        }
        if u32_coeff_is_mult(*coeff, p) {
            cost.coeff_mults += 1;
        }
        cost.adds += 1;
    }
    if rel.constant != 0 {
        cost.adds += 1;
    }
    cost
}

/// Cost of a max-quadratic relation with common-subexpression elimination on the inner linear
/// combinations. `materialized` records the canonical inner forms already built (shared across
/// gates): each distinct form pays its construction (coefficient scaling + additions) only once,
/// after which every quadratic term that uses it just multiplies (`a * L`) and accumulates.
fn max_quadratic_cse_cost(
    rel: &NoFieldMaxQuadraticGKRRelation,
    p: u32,
    materialized: &mut BTreeSet<Vec<(u32, GKRAddress)>>,
) -> EvalCost {
    let mut cost = EvalCost::default();
    for (_a, inner) in rel.quadratic_terms.iter() {
        // Canonical key for the inner linear form (drop zero coefficients, sort).
        let mut key: Vec<(u32, GKRAddress)> =
            inner.iter().filter(|(c, _)| *c != 0).copied().collect();
        if key.is_empty() {
            continue;
        }
        key.sort();
        // Build the inner sum only the first time we ever see this exact linear form.
        if materialized.insert(key.clone()) {
            for (coeff, _b) in key.iter() {
                if u32_coeff_is_mult(*coeff, p) {
                    cost.coeff_mults += 1;
                }
            }
            cost.adds += key.len() - 1; // sum the (already-scaled) terms
        }
        cost.product_mults += 1; // a * L
        cost.adds += 1; // accumulate into the result
    }
    for (coeff, _v) in rel.linear_terms.iter() {
        if *coeff == 0 {
            continue;
        }
        if u32_coeff_is_mult(*coeff, p) {
            cost.coeff_mults += 1;
        }
        cost.adds += 1;
    }
    if rel.constant != 0 {
        cost.adds += 1;
    }
    cost
}

/// Native cost of a linear relation `Σ c_k v_k + c`.
fn linear_native_cost(rel: &NoFieldLinearRelation, p: u32) -> EvalCost {
    let mut cost = EvalCost::default();
    for (coeff, _v) in rel.linear_terms.iter() {
        if *coeff == 0 {
            continue;
        }
        if u32_coeff_is_mult(*coeff, p) {
            cost.coeff_mults += 1;
        }
        cost.adds += 1;
    }
    if rel.constant != 0 {
        cost.adds += 1;
    }
    cost
}

/// Native arithmetic cost of one gate, before the batching fold. `None` for gate kinds we do not
/// model (so the caller can report coverage). Lookup gates use small, documented closed-form costs.
fn native_gate_cost(rel: &NoFieldGKRRelation, p: u32) -> Option<EvalCost> {
    let cost = match rel {
        NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input } => {
            max_quadratic_native_cost(input, p)
        }
        NoFieldGKRRelation::MaxQuadratic { input, .. } => max_quadratic_native_cost(input, p),
        NoFieldGKRRelation::LinearBaseFieldRelation { input, .. } => linear_native_cost(input, p),
        // A copy a(x) = Σ eq(x,y) a(y) carries no arithmetic of its own here.
        NoFieldGKRRelation::CopyInBaseField { .. }
        | NoFieldGKRRelation::CopyInExtensionField { .. } => EvalCost::default(),
        // A single product of two operands.
        NoFieldGKRRelation::InitialGrandProductFromCaches { .. }
        | NoFieldGKRRelation::InitialGrandProductWithoutCaches { .. }
        | NoFieldGKRRelation::TrivialProduct { .. } => EvalCost {
            product_mults: 1,
            coeff_mults: 0,
            adds: 0,
        },
        // 1/(a+γ) + 1/(b+γ): den = (a+γ)(b+γ), num = (a+γ) + (b+γ).
        NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { .. } => EvalCost {
            product_mults: 1,
            coeff_mults: 0,
            adds: 3,
        },
        // 1/(a+γ) + m/(s+γ): den = (a+γ)(s+γ), num = (s+γ) + m*(a+γ).
        NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup { .. } => EvalCost {
            product_mults: 2,
            coeff_mults: 0,
            adds: 3,
        },
        // a/b - c/d -> (num = a*d - c*b, den = b*d).
        NoFieldGKRRelation::LookupWithCachedDensAndSetup { .. } => EvalCost {
            product_mults: 3,
            coeff_mults: 0,
            adds: 1,
        },
        _ => return None,
    };
    Some(cost)
}

/// Number of outputs a gate writes (used for the batching-fold charge). Output-less enforced
/// constraints return 0 (the caller then charges a single fold).
fn num_outputs(rel: &NoFieldGKRRelation) -> usize {
    let mut outputs = BTreeSet::new();
    rel.dump_outputs(&mut outputs);
    outputs.len()
}

/// One operand-bearing monomial of the quadratic form, over dense variable indices.
struct AbstractTerm<E> {
    a: usize,
    b: Option<usize>,
    coeff: E,
}

/// A single instruction of the emitted evaluation program.
#[derive(Clone, Debug)]
pub(crate) enum EvalStep<E> {
    /// Read an input into a scratch slot. `reread` is true if this input had been loaded and evicted
    /// before — i.e. this load is a re-read, the thing we are trying to avoid.
    Load { address: GKRAddress, reread: bool },
    /// Drop a resident input from scratch to make room.
    Evict { address: GKRAddress },
    /// `acc += coeff * a * b` (both operands resident).
    MulAdd {
        a: GKRAddress,
        b: GKRAddress,
        coeff: E,
    },
    /// `acc += coeff * a` (operand resident).
    LinearAdd { address: GKRAddress, coeff: E },
}

/// The scheduled evaluation program plus its cost summary.
#[derive(Clone, Debug)]
pub(crate) struct EvaluationPlan<E> {
    pub(crate) scratch_space: usize,
    pub(crate) steps: Vec<EvalStep<E>>,
    /// Number of distinct inputs; each must be read at least once (the unavoidable floor).
    pub(crate) distinct_inputs: usize,
    /// Reads with no scratch at all: every operand of every term re-read each time.
    pub(crate) naive_reads: usize,
    pub(crate) total_reads: usize,
    pub(crate) re_reads: usize,
}

/// The evaluation program for a single independent partition (connected component).
#[derive(Clone, Debug)]
pub(crate) struct PartitionPlan<E> {
    pub(crate) members: Vec<GKRAddress>,
    pub(crate) steps: Vec<EvalStep<E>>,
    /// Whether the partition fits the input cache, i.e. needs zero re-reads.
    pub(crate) fits: bool,
    pub(crate) total_reads: usize,
    pub(crate) re_reads: usize,
}

/// Partitioned evaluation plan: independent partitions, free ones first, plus the cost summary.
#[derive(Clone, Debug)]
pub(crate) struct PartitionedPlan<E> {
    pub(crate) scratch_space: usize,
    pub(crate) partitions: Vec<PartitionPlan<E>>,
    pub(crate) distinct_inputs: usize,
    pub(crate) naive_reads: usize,
    pub(crate) total_reads: usize,
    pub(crate) re_reads: usize,
    pub(crate) fitting_partitions: usize,
    pub(crate) oversized_partitions: usize,
}

/// Which scratch-allocation strategy to use when scheduling a quadratic-form evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) enum Scheduler {
    /// Online greedy: pick the cheapest term to run next, evict the resident with the fewest
    /// *remaining* uses (a heuristic proxy for "needed furthest away").
    GreedySearch,
    /// Belady / MIN: keep the greedy's term order but use the provably optimal eviction for that
    /// fixed reference string — evict the resident whose *next* use is furthest in the future.
    #[default]
    Belady,
}

fn operands_of<E>(t: &AbstractTerm<E>) -> Vec<usize> {
    match t.b {
        Some(b) => vec![t.a, b],
        None => vec![t.a],
    }
}

/// Schedule an evaluation of `terms` over `addresses` within `scratch_space`, using `scheduler`.
///
/// Both strategies share the same term ordering (the greedy pass below); they differ only in the
/// eviction policy, so the comparison isolates eviction quality. See [`optimize_quadratic_evaluation`]
/// for the cost model.
fn schedule<E: Field>(
    addresses: &[GKRAddress],
    terms: &[AbstractTerm<E>],
    scratch_space: usize,
    scheduler: Scheduler,
) -> EvaluationPlan<E> {
    let (greedy_plan, order) = greedy_run(addresses, terms, scratch_space);
    match scheduler {
        Scheduler::GreedySearch => greedy_plan,
        Scheduler::Belady => belady_replay(addresses, terms, &order, scratch_space),
    }
}

/// Online greedy scheduler. Returns its plan and the order in which it executed the terms (so a
/// different eviction policy can be replayed over the same order).
fn greedy_run<E: Field>(
    addresses: &[GKRAddress],
    terms: &[AbstractTerm<E>],
    scratch_space: usize,
) -> (EvaluationPlan<E>, Vec<usize>) {
    let n_vars = addresses.len();
    // One scratch slot is permanently held by the accumulator intermediate.
    let input_capacity = scratch_space - 1;

    // Remaining future uses of each variable; the proxy for "needed furthest away".
    let mut remaining_uses = vec![0usize; n_vars];
    for t in terms.iter() {
        for op in operands_of(t) {
            remaining_uses[op] += 1;
        }
    }
    let naive_reads: usize = terms.iter().map(|t| operands_of(t).len()).sum();

    let mut resident: BTreeSet<usize> = BTreeSet::new();
    let mut loaded_before = vec![false; n_vars];
    let mut executed = vec![false; terms.len()];
    let mut remaining = terms.len();

    let mut steps = Vec::new();
    let mut order = Vec::with_capacity(terms.len());
    let mut total_reads = 0usize;
    let mut re_reads = 0usize;

    while remaining > 0 {
        // Pick the next term: fewest new loads, breaking ties towards loading the most-reused inputs.
        let mut best: Option<(usize, usize, i64)> = None; // (term, loads, -reuse)
        for (i, t) in terms.iter().enumerate() {
            if executed[i] {
                continue;
            }
            let ops = operands_of(t);
            let loads = ops.iter().filter(|op| !resident.contains(op)).count();
            let reuse: i64 = ops
                .iter()
                .filter(|op| !resident.contains(op))
                .map(|&op| remaining_uses[op] as i64)
                .sum();
            let key = (loads, -reuse);
            if best.is_none_or(|(_, bl, br)| key < (bl, br)) {
                best = Some((i, loads, -reuse));
            }
        }
        let (term_idx, _, _) = best.unwrap();
        let term = &terms[term_idx];
        let ops = operands_of(term);

        // Bring every missing operand into scratch, evicting low-future-use inputs as needed.
        for &op in ops.iter() {
            if resident.contains(&op) {
                continue;
            }
            while resident.len() >= input_capacity {
                let victim = resident
                    .iter()
                    .filter(|r| !ops.contains(r))
                    .copied()
                    .min_by_key(|r| remaining_uses[*r]);
                match victim {
                    Some(v) => {
                        resident.remove(&v);
                        steps.push(EvalStep::Evict {
                            address: addresses[v],
                        });
                    }
                    None => break,
                }
            }
            resident.insert(op);
            total_reads += 1;
            let reread = loaded_before[op];
            if reread {
                re_reads += 1;
            }
            loaded_before[op] = true;
            steps.push(EvalStep::Load {
                address: addresses[op],
                reread,
            });
        }

        emit_arithmetic(&mut steps, addresses, term);
        order.push(term_idx);
        executed[term_idx] = true;
        remaining -= 1;
        for op in ops {
            remaining_uses[op] -= 1;
        }
    }

    let plan = EvaluationPlan {
        scratch_space,
        steps,
        distinct_inputs: n_vars,
        naive_reads,
        total_reads,
        re_reads,
    };
    (plan, order)
}

/// Replay a fixed term `order` with Belady's optimal (MIN) eviction: when scratch is full, evict the
/// resident input whose next use in the remaining sequence is furthest away (or never).
fn belady_replay<E: Field>(
    addresses: &[GKRAddress],
    terms: &[AbstractTerm<E>],
    order: &[usize],
    scratch_space: usize,
) -> EvaluationPlan<E> {
    let n_vars = addresses.len();
    let input_capacity = scratch_space - 1;
    let naive_reads: usize = terms.iter().map(|t| operands_of(t).len()).sum();

    // For each variable, the ascending positions in `order` at which it is an operand.
    let mut occurrences: Vec<Vec<usize>> = vec![Vec::new(); n_vars];
    for (pos, &ti) in order.iter().enumerate() {
        for op in operands_of(&terms[ti]) {
            occurrences[op].push(pos);
        }
    }
    // Next position strictly after `pos` at which `v` is used, or usize::MAX if never again.
    let next_use = |v: usize, pos: usize| -> usize {
        let list = &occurrences[v];
        let idx = list.partition_point(|&p| p <= pos);
        list.get(idx).copied().unwrap_or(usize::MAX)
    };

    let mut resident: BTreeSet<usize> = BTreeSet::new();
    let mut loaded_before = vec![false; n_vars];
    let mut steps = Vec::new();
    let mut total_reads = 0usize;
    let mut re_reads = 0usize;

    for (pos, &term_idx) in order.iter().enumerate() {
        let term = &terms[term_idx];
        let ops = operands_of(term);
        for &op in ops.iter() {
            if resident.contains(&op) {
                continue;
            }
            while resident.len() >= input_capacity {
                let victim = resident
                    .iter()
                    .filter(|r| !ops.contains(r))
                    .copied()
                    .max_by_key(|&r| next_use(r, pos));
                match victim {
                    Some(v) => {
                        resident.remove(&v);
                        steps.push(EvalStep::Evict {
                            address: addresses[v],
                        });
                    }
                    None => break,
                }
            }
            resident.insert(op);
            total_reads += 1;
            let reread = loaded_before[op];
            if reread {
                re_reads += 1;
            }
            loaded_before[op] = true;
            steps.push(EvalStep::Load {
                address: addresses[op],
                reread,
            });
        }
        emit_arithmetic(&mut steps, addresses, term);
    }

    EvaluationPlan {
        scratch_space,
        steps,
        distinct_inputs: n_vars,
        naive_reads,
        total_reads,
        re_reads,
    }
}

fn emit_arithmetic<E: Field>(
    steps: &mut Vec<EvalStep<E>>,
    addresses: &[GKRAddress],
    term: &AbstractTerm<E>,
) {
    match term.b {
        Some(b) => steps.push(EvalStep::MulAdd {
            a: addresses[term.a],
            b: addresses[b],
            coeff: term.coeff,
        }),
        None => steps.push(EvalStep::LinearAdd {
            address: addresses[term.a],
            coeff: term.coeff,
        }),
    }
}

/// Result of partitioning the quadratic interaction graph into clusters.
///
/// Holds the two complementary views:
/// * `partitions`: cluster number -> all member [`GKRAddress`]es, each with the quadratic terms
///   (neighbour address + coefficient) of that cluster incident to it.
/// * `address_to_partitions`: [`GKRAddress`] -> every cluster it belongs to. More than one entry
///   means the address is *shared* across clusters (an overlap / separator variable).
#[derive(Clone, Debug)]
pub(crate) struct GraphPartitioning<E> {
    pub(crate) partitions: BTreeMap<usize, Vec<(GKRAddress, Vec<(GKRAddress, E)>)>>,
    pub(crate) address_to_partitions: BTreeMap<GKRAddress, Vec<usize>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClusterKind {
    /// A fully-isolated connected component of size 2 (Phase 1).
    IsolatedPair,
    /// A fully-isolated connected component of size 1 (no quadratic terms).
    Singleton,
    /// A cluster grown out of a larger component (Phase 2), possibly overlapping others.
    Clustered,
}

/// A single cluster: its member vertices and the quadratic terms (edges, canonical `u < v`) assigned
/// to it. Every assigned term has both endpoints among `vertices`, so the cluster is self-contained.
struct ClusterRaw<E> {
    vertices: BTreeSet<usize>,
    edges: Vec<(usize, usize, E)>,
    kind: ClusterKind,
}

/// Undirected graph over [`GKRAddress`]es with a dense internal vertex indexing. Each edge carries
/// the coefficient of the quadratic term that induced it.
struct AddressGraph<E> {
    addresses: Vec<GKRAddress>,
    index_of: BTreeMap<GKRAddress, usize>,
    adjacency: Vec<BTreeMap<usize, E>>,
}

impl<E: Field> AddressGraph<E> {
    fn new() -> Self {
        Self {
            addresses: Vec::new(),
            index_of: BTreeMap::new(),
            adjacency: Vec::new(),
        }
    }

    /// Add edges from one `quadratic_part_*` representation: for every key `a` and every
    /// `(b, coeff)` in its value vector we add an edge `a -- b` carrying `coeff` (self-loops are
    /// ignored).
    ///
    /// Can be called repeatedly to merge contributions from `base_by_base`, `base_by_ext` and
    /// `ext_by_ext` into the same graph; vertices are deduplicated and coefficients of a repeated
    /// edge are accumulated.
    fn add_quadratic_part<'a>(
        &mut self,
        terms: impl Iterator<Item = &'a (GKRAddress, Vec<(GKRAddress, E)>)>,
    ) where
        E: 'a,
    {
        for (a, neighbours) in terms {
            // make sure isolated keys still become vertices
            self.vertex(*a);
            for (b, coeff) in neighbours.iter() {
                self.add_edge(*a, *b, *coeff);
            }
        }
    }

    fn vertex(&mut self, address: GKRAddress) -> usize {
        if let Some(&idx) = self.index_of.get(&address) {
            return idx;
        }
        let idx = self.addresses.len();
        self.addresses.push(address);
        self.index_of.insert(address, idx);
        self.adjacency.push(BTreeMap::new());
        idx
    }

    fn add_edge(&mut self, a: GKRAddress, b: GKRAddress, coeff: E) {
        if a == b {
            return;
        }
        let a = self.vertex(a);
        let b = self.vertex(b);
        self.adjacency[a].entry(b).or_insert(E::ZERO).add_assign(&coeff);
        self.adjacency[b].entry(a).or_insert(E::ZERO).add_assign(&coeff);
    }

    /// Build the cluster list with the two-phase strategy:
    ///
    /// * **Phase 1** — every connected component of size <= 2 is emitted directly: size-2 components
    ///   are the fully-isolated pairs we want as many of as possible, size-1 are stray singletons.
    ///   These never overlap anything.
    /// * **Phase 2** — each larger component is greedily cut into connected clusters of roughly
    ///   `target_cluster_size` vertices (see [`greedy_cluster_component`]). Because every quadratic
    ///   term must stay wholly inside one cluster, a term straddling a cut forces both endpoints to
    ///   be shared, so clusters overlap on their boundary vertices; the greedy growth picks the
    ///   expansion vertices that add the fewest boundary edges to keep that overlap small.
    fn greedy_clusters(&self, target_cluster_size: usize) -> Vec<ClusterRaw<E>> {
        let mut clusters = Vec::new();
        for component in self.connected_components() {
            match component.len() {
                1 => {
                    let mut vertices = BTreeSet::new();
                    vertices.insert(component[0]);
                    clusters.push(ClusterRaw {
                        vertices,
                        edges: Vec::new(),
                        kind: ClusterKind::Singleton,
                    });
                }
                2 => {
                    let (u, v) = (component[0], component[1]);
                    let (lo, hi) = (u.min(v), u.max(v));
                    let coeff = self.adjacency[lo][&hi];
                    clusters.push(ClusterRaw {
                        vertices: [lo, hi].into_iter().collect(),
                        edges: vec![(lo, hi, coeff)],
                        kind: ClusterKind::IsolatedPair,
                    });
                }
                _ => {
                    clusters.extend(self.greedy_cluster_component(&component, target_cluster_size));
                }
            }
        }
        clusters
    }

    /// Greedily cut one (large) connected component into connected clusters of about
    /// `target_cluster_size` vertices, assigning every edge to exactly one cluster.
    ///
    /// Each cluster grows from a seed edge: we repeatedly absorb edges already fully inside the
    /// cluster (free, no new vertex), then expand to the neighbouring vertex with the smallest
    /// *external* degree (fewest edges leaving the current cluster) so the boundary — and hence the
    /// overlap with future clusters — stays minimal. Growth stops once the cluster reaches the
    /// target size; remaining edges seed the next cluster.
    fn greedy_cluster_component(
        &self,
        component: &[usize],
        target_cluster_size: usize,
    ) -> Vec<ClusterRaw<E>> {
        let target = target_cluster_size.max(2);
        // Canonical (u < v) edges of this component, still to be assigned.
        let mut unassigned: BTreeSet<(usize, usize)> = BTreeSet::new();
        for &u in component {
            for &v in self.adjacency[u].keys() {
                if u < v {
                    unassigned.insert((u, v));
                }
            }
        }

        let coeff_of = |lo: usize, hi: usize| self.adjacency[lo][&hi];
        let mut clusters = Vec::new();

        while !unassigned.is_empty() {
            // Seed with the unassigned edge whose endpoints have the smallest combined degree,
            // i.e. start growing from the periphery.
            let seed = *unassigned
                .iter()
                .min_by_key(|(u, v)| self.adjacency[*u].len() + self.adjacency[*v].len())
                .unwrap();
            unassigned.remove(&seed);
            let mut vertices: BTreeSet<usize> = [seed.0, seed.1].into_iter().collect();
            let mut edges: Vec<(usize, usize, E)> = vec![(seed.0, seed.1, coeff_of(seed.0, seed.1))];

            loop {
                // Absorb every unassigned edge that is already fully inside the cluster: it adds a
                // term for free without enlarging the vertex set.
                let internal: Vec<(usize, usize)> = unassigned
                    .iter()
                    .filter(|(u, v)| vertices.contains(u) && vertices.contains(v))
                    .copied()
                    .collect();
                for e in internal {
                    unassigned.remove(&e);
                    edges.push((e.0, e.1, coeff_of(e.0, e.1)));
                }

                if vertices.len() >= target {
                    break;
                }

                // Expand to the frontier vertex with the lowest external degree.
                let mut best: Option<(usize, (usize, usize), usize)> = None; // (outside, edge, score)
                for &(u, v) in unassigned.iter() {
                    let (inside, outside) = match (vertices.contains(&u), vertices.contains(&v)) {
                        (true, false) => (u, v),
                        (false, true) => (v, u),
                        _ => continue,
                    };
                    let _ = inside;
                    // External degree of `outside`: edges from it to vertices *not yet* in cluster.
                    let external = self.adjacency[outside]
                        .keys()
                        .filter(|w| !vertices.contains(w))
                        .count();
                    if best.is_none_or(|(_, _, s)| external < s) {
                        best = Some((outside, (u, v), external));
                    }
                }

                match best {
                    Some((outside, edge, _)) => {
                        vertices.insert(outside);
                        unassigned.remove(&edge);
                        edges.push((edge.0, edge.1, coeff_of(edge.0, edge.1)));
                    }
                    None => break,
                }
            }

            clusters.push(ClusterRaw {
                vertices,
                edges,
                kind: ClusterKind::Clustered,
            });
        }

        clusters
    }

    /// Materialise the two output maps from a cluster list.
    fn build_partitioning(&self, clusters: &[ClusterRaw<E>]) -> GraphPartitioning<E> {
        let mut partitions: BTreeMap<usize, Vec<(GKRAddress, Vec<(GKRAddress, E)>)>> =
            BTreeMap::new();
        let mut address_to_partitions: BTreeMap<GKRAddress, Vec<usize>> = BTreeMap::new();

        for (cluster_id, cluster) in clusters.iter().enumerate() {
            // Seed every member with an empty term list and record its cluster membership.
            let mut member_terms: BTreeMap<GKRAddress, Vec<(GKRAddress, E)>> = BTreeMap::new();
            for &v in cluster.vertices.iter() {
                member_terms.entry(self.addresses[v]).or_default();
                address_to_partitions
                    .entry(self.addresses[v])
                    .or_default()
                    .push(cluster_id);
            }
            // Attach each assigned term to both of its endpoints.
            for &(u, v, coeff) in cluster.edges.iter() {
                let (au, av) = (self.addresses[u], self.addresses[v]);
                member_terms.get_mut(&au).unwrap().push((av, coeff));
                member_terms.get_mut(&av).unwrap().push((au, coeff));
            }
            partitions.insert(cluster_id, member_terms.into_iter().collect());
        }

        GraphPartitioning {
            partitions,
            address_to_partitions,
        }
    }

    fn num_vertices(&self) -> usize {
        self.addresses.len()
    }

    fn num_edges(&self) -> usize {
        self.adjacency.iter().map(|nbs| nbs.len()).sum::<usize>() / 2
    }

    /// Connected components via iterative DFS. Each returned `Vec` lists the vertex indices of one
    /// component. Disjoint components can be processed completely independently.
    fn connected_components(&self) -> Vec<Vec<usize>> {
        let n = self.num_vertices();
        let mut component_of = vec![usize::MAX; n];
        let mut components = Vec::new();
        for start in 0..n {
            if component_of[start] != usize::MAX {
                continue;
            }
            let id = components.len();
            let mut members = Vec::new();
            let mut stack = vec![start];
            component_of[start] = id;
            while let Some(v) = stack.pop() {
                members.push(v);
                for &nb in self.adjacency[v].keys() {
                    if component_of[nb] == usize::MAX {
                        component_of[nb] = id;
                        stack.push(nb);
                    }
                }
            }
            components.push(members);
        }
        components
    }

}

#[cfg(test)]
mod test {
    use super::*;

    const USE_GKR_WITH_CACHES: bool = true;
    use crate::tests::gkr::deserialize_from_file;
    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};

    type F = BabyBearField;
    type E = BabyBearExt4;

    #[test]
    fn compare_gate_vs_batched_cost_in_circuit() {
        let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
            deserialize_from_file("../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json")
        } else {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
            )
        };

        let layer_idx = 0;
        let layer = &circuit.layers[layer_idx];

        let collector =
            KernelCollector::<F, E>::from_layer(layer, layer_idx, E::ONE, E::ONE, E::ONE, &[], 0);

        let cmp = collector.compare_gate_vs_batched_cost(layer);

        println!("\n===== batched (flattened) vs individual gates, layer {} =====", layer_idx);
        println!(
            "gates: {} ({} unmodeled)",
            cmp.num_gates, cmp.unmodeled_gates
        );
        println!("                       challenge-mults   internal-mults   adds");
        println!(
            "  batched:             {:>13}   {:>14}   {:>4}",
            cmp.batched_challenge_mults(),
            cmp.batched_internal_mults(),
            cmp.batched.adds,
        );
        println!(
            "  individual gates:    {:>13}   {:>14}   {:>4}",
            cmp.gate_challenge_mults(),
            cmp.gate_internal_mults(),
            cmp.gate_native.adds,
        );
        println!(
            "  gates (with CSE):    {:>13}   {:>14}   {:>4}",
            cmp.gate_challenge_mults(),
            cmp.gate_internal_mults_cse(),
            cmp.gate_native_cse.adds,
        );
        println!(
            "  delta (batched-gates):{:>+12}   {:>+14}   {:>+4}",
            cmp.batched_challenge_mults() as i64 - cmp.gate_challenge_mults() as i64,
            cmp.batched_internal_mults() as i64 - cmp.gate_internal_mults() as i64,
            cmp.batched.adds as i64 - cmp.gate_native.adds as i64,
        );
        println!(
            "CSE saved {} internal-mults and {} adds inside the max-quadratic gates",
            cmp.gate_internal_mults() as i64 - cmp.gate_internal_mults_cse() as i64,
            cmp.gate_native.adds as i64 - cmp.gate_native_cse.adds as i64,
        );

        assert_eq!(cmp.unmodeled_gates, 0, "all layer-0 gate kinds should be modeled");
        assert!(
            cmp.gate_internal_mults_cse() <= cmp.gate_internal_mults(),
            "CSE cannot increase internal multiplications"
        );
    }

    #[test]
    fn analyze_terms_in_circuit() {
        let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
            )
        } else {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
            )
        };

        let layer_idx = 0;
        let layer = &circuit.layers[layer_idx];

        let collector =
            KernelCollector::<F, E>::from_layer(layer, layer_idx, E::ONE, E::ONE, E::ONE, &[], 0);

        collector.analyze_terms();
    }

    #[test]
    fn partition_quadratic_graph_in_circuit() {
        let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
            )
        } else {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
            )
        };

        let layer_idx = 0;
        let layer = &circuit.layers[layer_idx];

        let collector =
            KernelCollector::<F, E>::from_layer(layer, layer_idx, E::ONE, E::ONE, E::ONE, &[], 0);

        let target_cluster_size = 9;
        let partitioning = collector.partition_quadratic_graph(target_cluster_size);

        println!("\n===== partition -> members and their quadratic terms =====");
        for (part, members) in partitioning.partitions.iter() {
            println!("partition {} ({} member(s)):", part, members.len());
            // Each quadratic term is stored on both endpoints; print every undirected term once.
            let mut printed = BTreeSet::new();
            for (address, terms) in members.iter() {
                println!("    {:?}", address);
                for (neighbour, coeff) in terms.iter() {
                    let key = (address.min(neighbour), address.max(neighbour));
                    if !printed.insert(key) {
                        continue;
                    }
                    println!("        * {:?} x {:?}  (coeff {})", address, neighbour, coeff);
                }
            }
        }

        println!("\n===== GKRAddress -> partition(s)  (multiple = shared/overlap) =====");
        for (address, parts) in partitioning.address_to_partitions.iter() {
            if parts.len() > 1 {
                println!("    {:?} -> partitions {:?}  (SHARED)", address, parts);
            } else {
                println!("    {:?} -> partition {}", address, parts[0]);
            }
        }
    }

    #[test]
    fn optimize_quadratic_evaluation_in_circuit() {
        let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
            deserialize_from_file("../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json")
        } else {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
            )
        };

        let layer_idx = 0;
        let layer = &circuit.layers[layer_idx];

        let collector =
            KernelCollector::<F, E>::from_layer(layer, layer_idx, E::ONE, E::ONE, E::ONE, &[], 0);

        let scratch_space = 8;
        let plan = collector.optimize_quadratic_evaluation(scratch_space, Scheduler::default());

        println!(
            "\n===== quadratic-form evaluation plan (scratch = {}, {} for inputs) =====",
            plan.scratch_space,
            plan.scratch_space - 1
        );
        for (i, step) in plan.steps.iter().enumerate() {
            match step {
                EvalStep::Load { address, reread } => println!(
                    "  {:>4}: LOAD   {:?}{}",
                    i,
                    address,
                    if *reread { "   (RE-READ)" } else { "" }
                ),
                EvalStep::Evict { address } => {
                    println!("  {:>4}: EVICT  {:?}", i, address)
                }
                EvalStep::MulAdd { a, b, coeff } => {
                    println!("  {:>4}: acc += {} * {:?} * {:?}", i, coeff, a, b)
                }
                EvalStep::LinearAdd { address, coeff } => {
                    println!("  {:>4}: acc += {} * {:?}", i, coeff, address)
                }
            }
        }

        println!(
            "\nfloor (distinct inputs) = {}, no-scratch reads = {}, plan reads = {} ({} of them re-reads)",
            plan.distinct_inputs, plan.naive_reads, plan.total_reads, plan.re_reads,
        );

        // Sanity: every input is read at least once, and we never beat the theoretical floor.
        assert!(plan.total_reads >= plan.distinct_inputs);
        assert!(plan.total_reads <= plan.naive_reads);
        assert_eq!(plan.total_reads, plan.distinct_inputs + plan.re_reads);
    }

    #[test]
    fn optimize_quadratic_evaluation_partitioned_in_circuit() {
        let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
            deserialize_from_file("../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json")
        } else {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
            )
        };

        let layer_idx = 0;
        let layer = &circuit.layers[layer_idx];

        let collector =
            KernelCollector::<F, E>::from_layer(layer, layer_idx, E::ONE, E::ONE, E::ONE, &[], 0);

        let scratch_space = 8;
        let plan =
            collector.optimize_quadratic_evaluation_partitioned(scratch_space, Scheduler::default());

        println!(
            "\n===== partitioned evaluation plan (scratch = {}, {} for inputs) =====",
            plan.scratch_space,
            plan.scratch_space - 1
        );
        println!(
            "{} partition(s): {} fit the cache (zero re-reads), {} oversized.",
            plan.partitions.len(),
            plan.fitting_partitions,
            plan.oversized_partitions,
        );

        for (p, part) in plan.partitions.iter().enumerate() {
            println!(
                "\n-- partition {} : {} member(s), {} ({} reads, {} re-reads) --",
                p,
                part.members.len(),
                if part.fits { "FITS" } else { "OVERSIZED" },
                part.total_reads,
                part.re_reads,
            );
            for (i, step) in part.steps.iter().enumerate() {
                match step {
                    EvalStep::Load { address, reread } => println!(
                        "  {:>4}: LOAD   {:?}{}",
                        i,
                        address,
                        if *reread { "   (RE-READ)" } else { "" }
                    ),
                    EvalStep::Evict { address } => println!("  {:>4}: EVICT  {:?}", i, address),
                    EvalStep::MulAdd { a, b, coeff } => {
                        println!("  {:>4}: acc += {} * {:?} * {:?}", i, coeff, a, b)
                    }
                    EvalStep::LinearAdd { address, coeff } => {
                        println!("  {:>4}: acc += {} * {:?}", i, coeff, address)
                    }
                }
            }
        }

        println!(
            "\nfloor (distinct inputs) = {}, no-scratch reads = {}, plan reads = {} ({} of them re-reads)",
            plan.distinct_inputs, plan.naive_reads, plan.total_reads, plan.re_reads,
        );

        // Re-reads can only come from oversized partitions.
        let reread_from_fitting: usize = plan
            .partitions
            .iter()
            .filter(|p| p.fits)
            .map(|p| p.re_reads)
            .sum();
        assert_eq!(reread_from_fitting, 0, "fitting partitions must never re-read");
        assert_eq!(plan.total_reads, plan.distinct_inputs + plan.re_reads);
    }

    #[test]
    fn sweep_scratch_vs_rereads() {
        let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
            deserialize_from_file("../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json")
        } else {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
            )
        };

        let layer_idx = 0;
        let layer = &circuit.layers[layer_idx];

        let collector =
            KernelCollector::<F, E>::from_layer(layer, layer_idx, E::ONE, E::ONE, E::ONE, &[], 0);

        // Compare both schedulers across the scratch range, for the global and partitioned modes.
        println!("scratch,distinct,greedy_rr,belady_rr,greedy_part_rr,belady_part_rr");
        for scratch in 4..=16 {
            let greedy = collector.optimize_quadratic_evaluation(scratch, Scheduler::GreedySearch);
            let belady = collector.optimize_quadratic_evaluation(scratch, Scheduler::Belady);
            let greedy_part = collector
                .optimize_quadratic_evaluation_partitioned(scratch, Scheduler::GreedySearch);
            let belady_part =
                collector.optimize_quadratic_evaluation_partitioned(scratch, Scheduler::Belady);
            println!(
                "{},{},{},{},{},{}",
                scratch,
                greedy.distinct_inputs,
                greedy.re_reads,
                belady.re_reads,
                greedy_part.re_reads,
                belady_part.re_reads,
            );
        }
    }
}
