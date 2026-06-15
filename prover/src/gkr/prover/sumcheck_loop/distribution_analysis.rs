use std::collections::BTreeSet;

use super::*;
use cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES;

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
    ) -> EvaluationPlan<E> {
        assert!(
            scratch_space >= 3,
            "need >=1 slot for the accumulator and >=2 for a quadratic term's operands"
        );
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

        // Flatten the whole description into one list of abstract terms over a dense variable set.
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

        greedy_schedule(&addresses, &terms, scratch_space)
    }
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

/// Greedy scratch-allocating scheduler. See [`optimize_quadratic_evaluation`] for the cost model.
fn greedy_schedule<E: Field>(
    addresses: &[GKRAddress],
    terms: &[AbstractTerm<E>],
    scratch_space: usize,
) -> EvaluationPlan<E> {
    let n_vars = addresses.len();
    // One scratch slot is permanently held by the accumulator intermediate.
    let input_capacity = scratch_space - 1;

    let operands = |t: &AbstractTerm<E>| -> Vec<usize> {
        match t.b {
            Some(b) => vec![t.a, b],
            None => vec![t.a],
        }
    };

    // Remaining future uses of each variable; the Belady proxy for "needed furthest away".
    let mut remaining_uses = vec![0usize; n_vars];
    for t in terms.iter() {
        for op in operands(t) {
            remaining_uses[op] += 1;
        }
    }
    let naive_reads: usize = terms.iter().map(|t| operands(t).len()).sum();

    let mut resident: BTreeSet<usize> = BTreeSet::new();
    let mut loaded_before = vec![false; n_vars];
    let mut executed = vec![false; terms.len()];
    let mut remaining = terms.len();

    let mut steps = Vec::new();
    let mut total_reads = 0usize;
    let mut re_reads = 0usize;

    while remaining > 0 {
        // Pick the next term: fewest new loads, breaking ties towards loading the most-reused inputs.
        let mut best: Option<(usize, usize, i64)> = None; // (term, loads, -reuse)
        for (i, t) in terms.iter().enumerate() {
            if executed[i] {
                continue;
            }
            let ops = operands(t);
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
        let ops = operands(term);

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

        // Emit the arithmetic and retire the term.
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
        executed[term_idx] = true;
        remaining -= 1;
        for op in ops {
            remaining_uses[op] -= 1;
        }
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
        let plan = collector.optimize_quadratic_evaluation(scratch_space);

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

        println!("scratch,input_slots,distinct_inputs,total_reads,re_reads");
        for scratch in 8..=32 {
            let plan = collector.optimize_quadratic_evaluation(scratch);
            println!(
                "{},{},{},{},{}",
                scratch,
                scratch - 1,
                plan.distinct_inputs,
                plan.total_reads,
                plan.re_reads,
            );
        }
    }
}
