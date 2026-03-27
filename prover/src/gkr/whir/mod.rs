// The original paper is overly complicated in it's notations, so here is a description.
// We will use capital letter for univariate polys, and small one for multivatiate, and same letter
// of different capitalization is just reinterpretation of one for another
// - Prover starts with oracle of evaluations F0 of the original poly F(X) at some smooth domain L0
// - also we assume that we have an original claim that F(Y) = Z, that can also we rewritten as sumcheck claim
// F(Y) = Z = f(y^0, y^1, y^2, ...) = \sum_{x} eq(x, y^0, y^1, y^2, ...) f(x) - our original sumcheck claim.
// If we sum over all the {x} in the right-hand side, but one, we can view it as a univariate f0(Y), and f0(0) + f0(1) == Z -
// all the standard sumcheck staff
// - Note that in the same manner we can express in-domain value F(omega^k) = \sum_{x} eq(x, omega^k decomposition over powers) f(x)
// - Prover and verifier can engage in more than 1 sumcheck steps (here the tradeoff is less steps later, but more accesses to F0 oracle)
// ---- Steps below are recursive, but we only use indexes 0/1 for clarity. Each step NUM_QUERIES also differs
// - At this moment we would have something like
// claim_0 = \sum_{x/folded coordiantes} eq(r1, r2, r3, x4, x5, ... y^0, y^1, y^2, y^4, ...) f(r1, r2, r3, x4, x5, ...)
// - Now prover sends an oracle F1 to f1(x4, x5, ...) = f(r1, r2, r3, x4, x5, ...) at domain L1. Note that "degree" of f1(x4, x5, ...)
// is smaller that of original f(x), but prover can decrease the rate for further iterations of the protocol
// - As in STIR, we want to perform out of domain sampling. So, we draw OOD point y1 and prover sends evaluation of f1(y1^0, y1^1, ...) = z1
// - Now prover also samples NUM_QUERIES indexes in the 3 (in our example) times folded image of L0. Those indexes trivially map
// into the |L0|/2^3 roots of unity. We will use notations Q_i for such indexes and corresponding roots of unity interchangeably
// - As in FRI, verifier has oracle access to f1(Q_i) by accessing 2^3 corresponding elements in F0 (at L0) and folding them.
// - We denote those values as G_i and in the original paper we do not need those values from prover YET, and instead they update our sumcheck claim formally at first,
// but it doesn't affect the protocol, and we will show that verification can be performed right away
// - start with the old one (prefactors aside)
// claim_0 = \sum_{x} eq(x, y^4, y^8, ...) f1(x)
// - add a contribution about f1(y1) = z1
// claim_0 + gamma^1 * z1 = \sum_{x} eq(x, y^4, y^8, ...) f1(x) + gamma^1 * \sum_{x} eq(x, y1^0, y1^1, ...) f1(x)
// - add NUM_QUERIES contribution about Q_i
// claim_0 + gamma^1 * z1 + \sum_{i = 0..NUM_QUERIES} gamma^{i + 1} G_i =
// = \sum_{x} eq(x, y^4, y^8, ...) f1(x) +
// + gamma^1 * \sum_{x} eq(x, y1^0, y1^1, ...) f1(x) +
// + \sum_{i = 0..NUM_QUERIES} gamma^{1+i} * \sum_{x} eq(x, Q_i) f1(x)
// - Those terms re-arrange nicely over f1(x)
// - To continue the sumcheck prover would send some univariate poly f2(Y), but as usual
// f2(0) + f2(1) == claim_0 + gamma^1 * z1 + \sum_{i = 0..NUM_QUERIES} gamma^{i + 1} G_i
// and verifier already has all the values to perform this check and forget about anything that happened before:
// - claim_0 comes from the previous work
// - z1 was sent by the prover
// - G_i are available via oracle access to F0 at L0 (in our example verifier needs 8 elements to fold 3 times and get those values)
// ---- Steps above are recursive until f_i(x) becomes "small-ish"
// - prover and verifier can engate in folding f1(x) few times until it becomes "small"
// - prover sends explicit form of the corresponding f_final(x)
// - same as above, we choose NUM_QUERIES_FINAL indexes, access previous step's oracle to get NUM_QUERIES_FINAL f1(x) values
// - Those values are checked to correspond to the explicit f_final(x) form
// - evaluate the last sumcheck explicitly
// - Due to complexity of such sumcheck (that drags various prefactors from previous rounds), most likely size of the final polynomial
// should be very small (much smaller compared to FRI case)

// NOTE: as we can choose rates somewhat independently from folding parameters, then for 100 bits of conjectured security we can do like
// let's say initially poly is 2^24
// - initial rate 1/2, and fold once - 100 queries, size 2^23
// - we discard all other polys from memory - RAM is no longer a problem, and next computations are cheap
// - rate 1/8, we do 33 queries and fold 4 times. Next step is 2^20
// - rate 1/64, we do 18 queries and fold 4 times. Next step is 2^16
// - rate 1/256, 13 queries, fold 4 times. Next step 2^12
// - rate 1/1024, 10 queries, fold 4 times. Next step 2^8
// - rate 1/4096, 8 queries, fold 4 times, output final 2^4 values

// NOTE: dealing with weight polys (that are EQ in our case only), and mixing it:
// - initially our kernel is claim0 = \sum_{X} eq(r1, r2, r3, ..., X) f(X)
// - prover sends a univariate poly of degree 3 such that p(0) = \sum_{X'} eq(r1, ..., 0, X') f(0, X'), p(1) = \sum_{X'} eq(r1, ..., 1, X') f(1, X'),
// and p(0) + p(1) = claim0
// - then we draw a challenge and evaluate p(alpha) = \sum_{X'} eq(r1, ...., alpha, X') f(alpha, X') =
// = \sum_{X''} eq(r1, ...., alpha, 0, X'') f(alpha, 0, X'') + eq(r1, ...., alpha, 1, X'') f(alpha, 1, X'')

use crate::gkr::prover::stages::stage1::{
    compute_column_major_lde_from_monomial_form,
    compute_column_major_monomial_form_from_main_domain_owned, ColumnMajorCosetBoundTracePart,
};
use crate::gkr::prover::transcript_utils::{
    add_whir_commitment_to_transcript, commit_field_els, draw_query_bits, draw_random_field_els,
};
use crate::gkr::sumcheck::eq_poly::{make_domain_eq_poly_in_full, make_eq_poly_in_full};
use crate::gkr::sumcheck::*;
use crate::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
use crate::gkr::PAR_THRESHOLD;
use crate::query_utils::assemble_query_index;
use crate::{gkr::prover::apply_row_wise, merkle_trees::ColumnMajorMerkleTreeConstructor};
use fft::{
    batch_inverse_inplace, bitreverse_enumeration_inplace, domain_generator_for_size,
    materialize_powers_serial_starting_with_one, Twiddles,
};
use field::{Field, FieldExtension, PrimeField, TwoAdicField};
use std::alloc::Global;
use std::sync::Arc;
use transcript::Seed;
use worker::{IterableWithGeometry, Worker};

pub mod hypercube_to_monomial;
pub mod queries;
pub mod whir_proof;

pub use self::queries::*;
pub use self::whir_proof::*;

#[derive(Debug)]
pub struct ColumnMajorBaseOracleForCoset<F: PrimeField + TwoAdicField> {
    pub original_values_normal_order: Vec<ColumnMajorCosetBoundTracePart<F, F>>, // num_columns
    pub offset: F,
    pub trace_len_log2: usize,
}

impl<F: PrimeField + TwoAdicField> ColumnMajorBaseOracleForCoset<F> {
    pub fn values_for_folded_index(&self, index: usize, values_per_leaf: usize) -> Vec<Vec<F>> {
        assert!(values_per_leaf.is_power_of_two());
        assert!(index < (1 << self.trace_len_log2) / values_per_leaf);
        let trace_len = 1 << self.trace_len_log2;

        let mut result: Vec<Vec<F>> = (0..values_per_leaf)
            .into_iter()
            .map(|_| Vec::with_capacity(self.original_values_normal_order.len()))
            .collect();

        match values_per_leaf {
            2 => {
                let offsets = [0, trace_len / 2];
                for src_poly in self.original_values_normal_order.iter() {
                    for (j, offset) in offsets.iter().enumerate() {
                        let i = *offset + index;
                        let value = src_poly.column[i];
                        result[j].push(value);
                    }
                }
            }
            a @ _ => {
                panic!("unsupported: {} values per leaf", a);
            }
        }

        result
    }
}

#[derive(Debug)]
pub struct ColumnMajorBaseOracleForLDE<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    pub cosets: Vec<ColumnMajorBaseOracleForCoset<F>>,
    pub tree: T,
    pub values_per_leaf: usize,
    pub trace_len_log2: usize,
}

impl<F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>>
    ColumnMajorBaseOracleForLDE<F, T>
{
    pub fn num_columns(&self) -> usize {
        self.cosets[0].original_values_normal_order.len()
    }

    pub fn query_for_folded_index(
        &self,
        index: usize,
    ) -> (usize, Vec<Vec<F>>, BaseFieldQuery<F, T>) {
        let coset_index = index & (self.cosets.len() - 1);
        let internal_index = index / self.cosets.len();
        assert!(internal_index < (1 << self.trace_len_log2) / self.values_per_leaf);
        let values =
            self.cosets[coset_index].values_for_folded_index(internal_index, self.values_per_leaf);

        let (_, path) = self.tree.get_proof(index);
        let query = BaseFieldQuery::<F, T> {
            index,
            leaf_values_concatenated: values.iter().flatten().copied().collect(),
            path,
            _marker: core::marker::PhantomData,
        };
        (coset_index, values, query)
    }
}

#[derive(Debug)]
pub struct ColumnMajorExtensionOracleForCoset<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
> {
    pub values_normal_order: ColumnMajorCosetBoundTracePart<F, E>, // single column
}

fn offsets_for_leaf_construction<const N: usize>(trace_len: usize) -> [usize; N] {
    assert!(trace_len.is_power_of_two());
    assert!(N.is_power_of_two());
    let mut result = [0; N];
    let stride = trace_len / N;
    for i in 0..N {
        result[i] = stride * i;
    }
    bitreverse_enumeration_inplace(&mut result);

    result
}

pub(crate) fn offsets_vec_for_leaf_construction(trace_len: usize, combine_by: usize) -> Vec<usize> {
    assert!(trace_len.is_power_of_two());
    assert!(combine_by.is_power_of_two());
    let mut result = Vec::with_capacity(combine_by);
    let stride = trace_len / combine_by;
    for i in 0..combine_by {
        result.push(stride * i);
    }
    bitreverse_enumeration_inplace(&mut result);

    result
}

impl<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>
    ColumnMajorExtensionOracleForCoset<F, E>
{
    pub fn values_for_folded_index(&self, index: usize, values_per_leaf: usize) -> Vec<E> {
        let trace_len = self.values_normal_order.column.len() as usize;
        assert!(values_per_leaf.is_power_of_two());
        assert!(
            index < trace_len / values_per_leaf,
            "folded index {} is too large for a coset of size 2^{} and {} values packed per leaf",
            index,
            trace_len.trailing_zeros(),
            values_per_leaf
        );

        let mut result: Vec<E> = Vec::with_capacity(values_per_leaf);

        match values_per_leaf {
            2 => {
                let offsets = offsets_for_leaf_construction::<2>(trace_len);
                for offset in offsets.iter() {
                    let i = *offset + index;
                    let value = self.values_normal_order.column[i];
                    result.push(value);
                }
            }
            4 => {
                let offsets = offsets_for_leaf_construction::<4>(trace_len);
                for offset in offsets.iter() {
                    let i = *offset + index;
                    let value = self.values_normal_order.column[i];
                    result.push(value);
                }
            }
            8 => {
                let offsets = offsets_for_leaf_construction::<8>(trace_len);
                for offset in offsets.iter() {
                    let i = *offset + index;
                    let value = self.values_normal_order.column[i];
                    result.push(value);
                }
            }
            16 => {
                let offsets = offsets_for_leaf_construction::<16>(trace_len);
                for offset in offsets.iter() {
                    let i = *offset + index;
                    let value = self.values_normal_order.column[i];
                    result.push(value);
                }
            }
            a @ _ => {
                panic!("unsupported: {} values per leaf", a);
            }
        }

        result
    }
}

#[derive(Debug)]
pub struct ColumnMajorExtensionOracleForLDE<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    pub cosets: Vec<ColumnMajorExtensionOracleForCoset<F, E>>,
    pub tree: T,
    pub values_per_leaf: usize,
    pub trace_len_log2: usize,
}

impl<
        F: PrimeField + TwoAdicField,
        E: FieldExtension<F> + Field,
        T: ColumnMajorMerkleTreeConstructor<F>,
    > ColumnMajorExtensionOracleForLDE<F, E, T>
{
    pub fn query_for_folded_index(
        &self,
        index: usize,
    ) -> (usize, Vec<E>, ExtensionFieldQuery<F, E, T>) {
        let coset_index = index & (self.cosets.len() - 1);
        let internal_index = index / self.cosets.len();
        let values =
            self.cosets[coset_index].values_for_folded_index(internal_index, self.values_per_leaf);
        let (_leaf_hash, path) = self.tree.get_proof(index);
        let query = ExtensionFieldQuery {
            index,
            leaf_values_concatenated: values.clone(),
            path,
            _marker: core::marker::PhantomData,
        };
        (coset_index, values, query)
    }
}

pub fn whir_fold<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    mem_oracle: ColumnMajorBaseOracleForLDE<F, T>,
    mem_polys_claims: Vec<E>,
    wit_oracle: ColumnMajorBaseOracleForLDE<F, T>,
    wit_polys_claims: Vec<E>,
    setup_oracle: &ColumnMajorBaseOracleForLDE<F, T>,
    setup_polys_claims: Vec<E>,
    original_evaluation_point: Vec<E>,
    original_lde_factor: usize,
    batching_challenge: E,
    whir_steps_schedule: Vec<usize>,
    whir_queries_schedule: Vec<usize>,
    whir_steps_lde_factors: Vec<usize>,
    whir_pow_schedule: Vec<u32>,
    twiddles: &Twiddles<F, Global>,
    mut transcript_seed: Seed,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
) -> WhirPolyCommitProof<F, E, T>
where
    [(); E::DEGREE]: Sized,
{
    let two_inv = F::from_u32_unchecked(2).inverse().unwrap();

    let oracle_refs = [&mem_oracle, &wit_oracle, setup_oracle];
    let evals_refs = [&mem_polys_claims, &wit_polys_claims, &setup_polys_claims];

    let mut eq_polys = make_eq_poly_in_full::<E>(&original_evaluation_point[..], worker);
    let mut eq_poly_box = eq_polys.pop().unwrap();

    #[cfg(feature = "gkr_self_checks")]
    {
        // just blindly compute consistency of RS oracles and evaluation points
        for (j, (rs, evals)) in oracle_refs.iter().zip(evals_refs.iter()).enumerate() {
            for (i, eval) in evals.iter().enumerate() {
                let main_domain_evals =
                    rs.cosets[0].original_values_normal_order[i].column[..].to_vec();
                let monomial_form = compute_column_major_monomial_form_from_main_domain_owned(
                    main_domain_evals,
                    twiddles,
                );
                assert_eq!(monomial_form.len(), 1 << trace_len_log2);
                let mut sumcheck_evals = monomial_form;
                multivariate_coeffs_into_hypercube_evals(
                    &mut sumcheck_evals,
                    trace_len_log2 as u32,
                );
                bitreverse_enumeration_inplace(&mut sumcheck_evals);
                use crate::gkr::whir::eq_poly::evaluate_with_precomputed_eq;
                let recomputed_claim =
                    evaluate_with_precomputed_eq(&sumcheck_evals, &eq_poly_box[..]);
                assert_eq!(
                    recomputed_claim, *eval,
                    "claim recomputation diverged for poly {} in oracle set {}",
                    i, j
                );
            }
        }
    }

    let mut commitments = Vec::with_capacity(3);
    for i in 0..3 {
        let t = WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: oracle_refs[i].tree.get_cap(),
                _marker: core::marker::PhantomData,
            },
            num_columns: oracle_refs[i].num_columns(),
            evals: evals_refs[i].clone(),
            queries: vec![],
        };
        commitments.push(t);
    }

    let [memory_commitment, witness_commitment, setup_commitment] = commitments.try_into().unwrap();

    let mut proof = WhirPolyCommitProof {
        witness_commitment,
        memory_commitment,
        setup_commitment,
        sumcheck_polys: vec![],
        intermediate_whir_oracles: Vec::with_capacity(whir_steps_lde_factors.len()),
        ood_samples: vec![],
        pow_nonces: vec![],
        final_monomials: vec![],
    };

    let mut final_poly_log2 = trace_len_log2;
    for el in whir_steps_schedule.iter() {
        assert!(*el <= final_poly_log2);
        final_poly_log2 -= *el;
    }

    assert!(original_lde_factor.is_power_of_two());
    let num_whir_steps = whir_steps_lde_factors.len();
    assert_eq!(whir_steps_schedule.len(), whir_steps_lde_factors.len() + 1);
    assert_eq!(whir_steps_schedule.len(), whir_queries_schedule.len());
    assert_eq!(whir_steps_schedule.len(), whir_pow_schedule.len());

    let mut rs_oracle;

    // first compute batched poly. We do compute it on main domain only, and then FFT,
    // especially if we are going to offload cosets from the original commitment to disk instead of keeping in RAM

    let total_base_oracles = oracle_refs.iter().map(|el| el.num_columns()).sum();
    assert_eq!(
        total_base_oracles,
        evals_refs.iter().map(|el| el.len()).sum::<usize>()
    );
    for (a, b) in oracle_refs.iter().zip(evals_refs.iter()) {
        assert_eq!(a.cosets[0].original_values_normal_order.len(), b.len());
    }

    let challenge_powers = materialize_powers_serial_starting_with_one::<E, Global>(
        batching_challenge,
        total_base_oracles,
    );

    let (base_mem_powers, rest) = challenge_powers.split_at(evals_refs[0].len());
    let (base_witness_powers, base_setup_powers) = rest.split_at(evals_refs[1].len());
    assert_eq!(base_setup_powers.len(), evals_refs[2].len());

    let batch_challenges = [
        base_mem_powers.to_vec(),
        base_witness_powers.to_vec(),
        base_setup_powers.to_vec(),
    ];

    let mut batched_poly_on_main_domain = vec![E::ZERO; 1 << trace_len_log2];

    apply_row_wise::<F, E>(
        vec![],
        vec![&mut batched_poly_on_main_domain],
        1 << trace_len_log2,
        worker,
        |_, dest, chunk_start, chunk_size| {
            assert_eq!(dest.len(), 1);
            let mut dest = dest;
            let dest = dest.pop().unwrap();
            for (challenges_set, values_set) in [
                (
                    base_mem_powers,
                    &oracle_refs[0].cosets[0].original_values_normal_order,
                ),
                (
                    base_witness_powers,
                    &oracle_refs[1].cosets[0].original_values_normal_order,
                ),
                (
                    base_setup_powers,
                    &oracle_refs[2].cosets[0].original_values_normal_order,
                ),
            ] {
                assert_eq!(challenges_set.len(), values_set.len());
                for (batch_challenge, base_value) in challenges_set.iter().zip(values_set.iter()) {
                    let src = &base_value.column[..]; // main domain only
                    assert_eq!(src.len(), 1 << trace_len_log2);
                    for i in 0..chunk_size {
                        let mut result = *batch_challenge;
                        result.mul_assign_by_base(&src[chunk_start + i]);
                        dest[i].add_assign(&result);
                    }
                }
            }
        },
    );

    let monomial_form = compute_column_major_monomial_form_from_main_domain_owned(
        batched_poly_on_main_domain,
        twiddles,
    );

    assert_eq!(monomial_form.len(), 1 << trace_len_log2);

    let mut sumcheck_evals = monomial_form.clone();
    multivariate_coeffs_into_hypercube_evals(
        &mut sumcheck_evals,
        monomial_form.len().trailing_zeros(),
    );
    bitreverse_enumeration_inplace(&mut sumcheck_evals);

    let mut batched_claim = E::ZERO;
    for (challenges_set, values_set) in [base_mem_powers, base_witness_powers, base_setup_powers]
        .into_iter()
        .zip(evals_refs.into_iter())
    {
        assert_eq!(challenges_set.len(), values_set.len());
        for (a, b) in challenges_set.iter().zip(values_set.into_iter()) {
            let mut result = *b;
            result.mul_assign(&a);
            batched_claim.add_assign(&result);
        }
    }
    drop(mem_polys_claims);
    drop(wit_polys_claims);
    drop(setup_polys_claims);

    let mut query_references = vec![];

    // our initial sumcheck claim is `batched_claim` = \sum_{hypercube} eq(x, `original_evaluation_point`) batched_poly(x)

    let num_rounds = whir_steps_schedule.len();
    assert!(num_rounds >= 2);

    let mut whir_steps_schedule = whir_steps_schedule.into_iter().peekable();
    let mut whir_queries_schedule = whir_queries_schedule.into_iter();
    let mut whir_steps_lde_factors = whir_steps_lde_factors.into_iter();
    let mut whir_pow_schedule = whir_pow_schedule.into_iter();

    // as we will eventually continue to mix-in additional equality polys into sumcheck kernel,
    // so we can NOT easily use the same trick with splitting out eq poly highest coordinate in sumcheck.
    // So we make EQ poly explicitly, and then we will update it after every step, and use naively

    let mut eq_poly = &mut eq_poly_box[..];
    drop(eq_polys);

    let mut sumchecked_poly_evaluation_form_vec = sumcheck_evals;
    let mut sumchecked_poly_evaluation_form = &mut sumchecked_poly_evaluation_form_vec[..];
    let mut sumchecked_poly_monomial_form = monomial_form;
    let mut monomial_form_buffer = Vec::with_capacity(sumchecked_poly_monomial_form.len());

    let mut claim = batched_claim;

    #[cfg(feature = "gkr_self_checks")]
    {
        let recomputed_claim = dot_product(&sumchecked_poly_evaluation_form, &eq_poly, worker);
        assert_eq!(recomputed_claim, claim);
    }

    assert_eq!(eq_poly.len(), sumchecked_poly_evaluation_form.len());
    assert_eq!(eq_poly.len(), sumchecked_poly_monomial_form.len());

    let mut folding_challenges = vec![];
    let mut delinearization_challenges_per_round = vec![];

    let mut poly_size_log2 = trace_len_log2;

    // initial round where we fold and query existing oracles
    {
        let num_initial_folding_rounds = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let pow_bits = whir_pow_schedule.next().unwrap();
        println!("Initial round: fold by {}", 1 << num_initial_folding_rounds);

        assert!(num_initial_folding_rounds <= poly_size_log2);
        let rs_domain_log2 = trace_len_log2 + (original_lde_factor.trailing_zeros() as usize);
        let query_domain_log2 = rs_domain_log2 - num_initial_folding_rounds;

        // Even though we can do all the same trick as in our GKR kernels and only evaluate sum of half-size,
        // instead we naively evaluate at 0 and 1, and use input claim to get the monomial form via Lagrange interpolation

        for el in oracle_refs.iter() {
            assert_eq!(el.values_per_leaf, 1 << num_initial_folding_rounds);
        }
        let mut folding_challenges_in_round = vec![];

        for _ in 0..num_initial_folding_rounds {
            let (f0, f1, f_half) = special_three_point_eval(
                &sumchecked_poly_evaluation_form[..],
                &eq_poly[..],
                worker,
            );
            let evaluation_point = E::from_base(two_inv);
            let univariate_coeffs = special_lagrange_interpolate(f0, f1, f_half, evaluation_point);
            // commit
            proof.sumcheck_polys.push(univariate_coeffs);
            commit_field_els(&mut transcript_seed, &univariate_coeffs);

            #[cfg(feature = "gkr_self_checks")]
            {
                let s0 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ZERO);
                assert_eq!(s0, f0);
                let s1 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ONE);
                assert_eq!(s1, f1);
                let s_half = evaluate_small_univariate_poly(&univariate_coeffs, &evaluation_point);
                assert_eq!(s_half, f_half);
                let mut v = s0;
                v.add_assign(&s1);
                assert_eq!(v, claim);
            }

            // draw folding challenge
            let folding_challenges = draw_random_field_els(&mut transcript_seed, 1);
            let folding_challenge = folding_challenges[0];
            folding_challenges_in_round.push(folding_challenge);

            let next_claim = evaluate_small_univariate_poly(&univariate_coeffs, &folding_challenge);
            claim = next_claim;
            // and fold the poly itself - both multivariate evals mapping, and monomial form

            fold_monomial_form(
                &mut sumchecked_poly_monomial_form,
                &mut monomial_form_buffer,
                &folding_challenge,
                worker,
            );

            sumchecked_poly_evaluation_form = fold_evaluation_form(
                &mut sumchecked_poly_evaluation_form[..],
                &folding_challenge,
                worker,
            );

            assert_eq!(
                sumchecked_poly_monomial_form.len(),
                sumchecked_poly_evaluation_form.len()
            );

            #[cfg(feature = "gkr_self_checks")]
            {
                let mut source = sumchecked_poly_monomial_form.clone();
                multivariate_coeffs_into_hypercube_evals(
                    &mut source,
                    sumchecked_poly_monomial_form.len().trailing_zeros(),
                );
                bitreverse_enumeration_inplace(&mut source);
                assert_eq!(source, sumchecked_poly_evaluation_form);
            }

            // and so we fold equality poly too
            eq_poly = fold_eq_poly(eq_poly, &folding_challenge, worker);
            assert_eq!(sumchecked_poly_evaluation_form.len(), eq_poly.len());
        }
        poly_size_log2 -= num_initial_folding_rounds;

        assert_eq!(sumchecked_poly_evaluation_form.len(), 1 << poly_size_log2);
        assert_eq!(sumchecked_poly_monomial_form.len(), 1 << poly_size_log2);
        assert_eq!(eq_poly.len(), 1 << poly_size_log2);

        #[cfg(feature = "gkr_self_checks")]
        {
            let full_sum = dot_product(&sumchecked_poly_evaluation_form, &eq_poly, worker);
            assert_eq!(full_sum, claim);
        }

        folding_challenges.push(folding_challenges_in_round.clone());

        // compute RS for folded one (we will NOT query it this round)
        {
            let lde_factor = whir_steps_lde_factors.next().unwrap();
            let rs = compute_column_major_lde_from_monomial_form(
                &sumchecked_poly_monomial_form,
                twiddles,
                lde_factor,
                Some(worker),
            );
            let next_folding_steps = *whir_steps_schedule.peek().unwrap();
            let next_oracle = commit_single_ext_poly::<F, E, T>(
                rs,
                1 << next_folding_steps,
                tree_cap_size,
                worker,
            );
            let c = WhirIntermediateCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap: next_oracle.tree.get_cap(),
                    _marker: core::marker::PhantomData,
                },
                queries: vec![],
            };
            add_whir_commitment_to_transcript(&mut transcript_seed, &c.commitment);
            proof.intermediate_whir_oracles.push(c);
            rs_oracle = next_oracle;
        }

        let mut contributions_to_eq_poly = vec![];
        let mut contributions_to_eq_poly_with_base_points = vec![];

        // draw OOD sample
        let ood_points: Vec<E> = draw_random_field_els(&mut transcript_seed, 1);
        let ood_point = ood_points[0];
        // compute OOD value
        let ood_value =
            evaluate_monomial_form(&sumchecked_poly_monomial_form[..], &ood_point, worker);
        commit_field_els(&mut transcript_seed, &[ood_value]);
        #[cfg(feature = "gkr_self_checks")]
        {
            let pows = make_pows(
                ood_point,
                sumchecked_poly_evaluation_form.len().trailing_zeros() as usize,
            );
            let value = evaluate_multivariate(&sumchecked_poly_evaluation_form, &pows, worker);
            assert_eq!(value, ood_value);
        }

        proof.ood_samples.push(ood_value);

        // now can draw challenges

        // and we can immediatelly query all the original oracles, and drop them. For that we need to draw indexes
        let query_domain_size = 1u64 << query_domain_log2;

        let query_domain_generator = domain_generator_for_size::<F>(query_domain_size);
        let input_domain_size = 1u64 << rs_domain_log2;
        let extended_generator = domain_generator_for_size::<F>(input_domain_size);

        // High powers
        let set_generator = domain_generator_for_size::<F>(1u64 << num_initial_folding_rounds);
        let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<F, Global>(
            set_generator.inverse().unwrap(),
            1 << (num_initial_folding_rounds - 1),
        );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);

        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        let num_bits_for_queries = num_queries * query_index_bits;
        let (nonce, mut bit_source) =
            draw_query_bits(&mut transcript_seed, num_bits_for_queries, pow_bits, worker);
        proof.pow_nonces.push(nonce);

        let mut query_indexes = vec![];
        for _ in 0..num_queries {
            // query index is power for omega^k expression, where omega^{`input_domain_size`} == 1
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            query_indexes.push(query_index);
        }

        // and delinearization challenge
        let delinearization_challenges: Vec<E> = draw_random_field_els(&mut transcript_seed, 1);
        let delinearization_challenge = delinearization_challenges[0];
        delinearization_challenges_per_round.push(delinearization_challenge);

        // we will have OOD sample contribution
        contributions_to_eq_poly.push((ood_point, delinearization_challenge));

        let mut claim_correction = E::ZERO;
        {
            let mut t = ood_value;
            t.mul_assign(&delinearization_challenge);
            claim_correction.add_assign(&t);
        }
        let mut current_delinearization_challenge = delinearization_challenge;
        current_delinearization_challenge.square();

        for &query_index in query_indexes.iter() {
            assert!(query_index < query_domain_size as usize);
            let query_point = query_domain_generator.pow(query_index as u32);

            // we have a query point, and now we need to understand "preimages" for it
            // assume that we have a query point omega_q ^ i, and we fold K times.
            // Then what we need is a set of points omega^{0 << (log(query_domain)) || i }, omega^{1 << (log(query_domain)) || i}, etc
            // where omega = root(omega_q, 2^K)

            // So for "base root" we take omega^i from the notations above, and when we fold we multiply it by root(1, 2^K)

            // get original leaf, compute batched, and then folded value
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let mut batched_evals = vec![E::ZERO; oracle_refs[0].values_per_leaf];
            for (set_idx, (oracle, batching_challenges)) in
                oracle_refs.iter().zip(batch_challenges.iter()).enumerate()
            {
                assert_eq!(
                    oracle.cosets[0].original_values_normal_order.len(),
                    batching_challenges.len()
                );
                let (_idx, leaf, query) = oracle.query_for_folded_index(query_index);
                match set_idx {
                    0 => {
                        proof.memory_commitment.queries.push(query);
                    }
                    1 => {
                        proof.witness_commitment.queries.push(query);
                    }
                    2 => {
                        proof.setup_commitment.queries.push(query);
                    }
                    _ => {
                        unreachable!()
                    }
                }
                assert_eq!(batched_evals.len(), leaf.len());
                for (dst, src) in batched_evals.iter_mut().zip(leaf.iter()) {
                    assert_eq!(src.len(), batching_challenges.len());
                    for (a, b) in src.iter().zip(batching_challenges.iter()) {
                        let mut t = *b;
                        t.mul_assign_by_base(a);
                        dst.add_assign(&t);
                    }
                }
            }

            let folded = fold_coset(
                batched_evals,
                num_initial_folding_rounds,
                &folding_challenges_in_round,
                &base_root_inv,
                &high_powers_offsets,
                &two_inv,
            );

            query_references.push((query_index, query_point, folded));

            // and add into sumcheck claim
            contributions_to_eq_poly_with_base_points
                .push((query_point, delinearization_challenge));
            {
                let mut t = folded;
                t.mul_assign(&delinearization_challenge);
                claim_correction.add_assign(&t);
            }
            current_delinearization_challenge.mul_assign(&delinearization_challenge);
        }

        #[cfg(feature = "gkr_self_checks")]
        {
            let omega = domain_generator_for_size::<F>(query_domain_size);
            for (i, &query_index) in query_indexes.iter().enumerate() {
                let root = omega.pow(query_index as u32);
                let eval_from_monomial = evaluate_monomial_form(
                    &sumchecked_poly_monomial_form,
                    &E::from_base(root),
                    worker,
                );
                assert_eq!(
                    (query_index, root, eval_from_monomial),
                    query_references[i],
                    "diverged at query {}",
                    i
                );
                let pows = make_pows(
                    root,
                    sumchecked_poly_evaluation_form.len().trailing_zeros() as usize,
                );
                let eval_from_multivariate =
                    evaluate_multivariate_at_base(&sumchecked_poly_evaluation_form, &pows, worker);
                assert_eq!(eval_from_monomial, eval_from_multivariate);
            }
            query_references.clear();
        }
        #[cfg(not(feature = "gkr_self_checks"))]
        query_references.clear();

        drop(mem_oracle);
        drop(wit_oracle);

        // we now update the equality poly - initially we had eq(X, original_evalution_point), from which we folded few coordinates.
        // Now we should add more terms there to reflect OOD and in-domain samples
        update_eq_poly(
            eq_poly,
            &contributions_to_eq_poly,
            &contributions_to_eq_poly_with_base_points,
            worker,
        );

        // and remember new sumcheck claim
        claim.add_assign(&claim_correction);
    }

    let num_internal_whir_steps = num_whir_steps - 1;
    println!(
        "Initial queries and folding are complete, now can proceed into {} internal rounds",
        num_internal_whir_steps
    );

    // now we step into recursive procesure over one batched polynomial and it's evals. Our sequence is
    // - fold
    // - RS code word computation and commit
    // - query previous(!) RS oracle
    // - update claim and eq poly
    for internal_round in 0..num_internal_whir_steps {
        // commit
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let pow_bits = whir_pow_schedule.next().unwrap();
        assert!(num_folding_steps <= poly_size_log2);

        println!(
            "Internal round {}: fold by {}",
            internal_round,
            1 << num_folding_steps
        );

        let rs_domain_log2 = poly_size_log2 + (rs_oracle.cosets.len().trailing_zeros() as usize);
        let query_domain_log2 = rs_domain_log2 - num_folding_steps;

        // fold

        // NOTE: we can no longer use the fact that sumcheck kernel is simple as \sum_X eq(r, X) p(X),
        // and so to send degree 2 poly to the verifier we need to compute such kernel at 3 points and interpolate.
        // As our hypercube is 0/1, then we choose to compute at 0, 1 and 1/2

        // eval(1/2) = \sum_{X} multilinear(1/2, X) * p(1/2, X) = 1/4 \sum_{X} (multilinear(1, X) + multilinear(0, X)) * (P(1, X) + P(0, X))

        let mut folding_challenges_in_round = Vec::with_capacity(num_folding_steps);

        for _ in 0..num_folding_steps {
            let (f0, f1, f_half) = special_three_point_eval(
                &sumchecked_poly_evaluation_form[..],
                &eq_poly[..],
                worker,
            );
            let evaluation_point = E::from_base(two_inv);
            let univariate_coeffs = special_lagrange_interpolate(f0, f1, f_half, evaluation_point);
            // commit
            proof.sumcheck_polys.push(univariate_coeffs);
            commit_field_els(&mut transcript_seed, &univariate_coeffs);

            #[cfg(feature = "gkr_self_checks")]
            {
                let s0 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ZERO);
                assert_eq!(s0, f0);
                let s1 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ONE);
                assert_eq!(s1, f1);
                let s_half = evaluate_small_univariate_poly(&univariate_coeffs, &evaluation_point);
                assert_eq!(s_half, f_half);
                let mut v = s0;
                v.add_assign(&s1);
                assert_eq!(v, claim);
            }

            let folding_challenges = draw_random_field_els(&mut transcript_seed, 1);
            let folding_challenge = folding_challenges[0];
            folding_challenges_in_round.push(folding_challenge);

            let next_claim = evaluate_small_univariate_poly(&univariate_coeffs, &folding_challenge);
            claim = next_claim;
            // and fold the poly itself - both multivariate evals mapping, and monomial form

            fold_monomial_form(
                &mut sumchecked_poly_monomial_form,
                &mut monomial_form_buffer,
                &folding_challenge,
                worker,
            );

            sumchecked_poly_evaluation_form = fold_evaluation_form(
                &mut sumchecked_poly_evaluation_form[..],
                &folding_challenge,
                worker,
            );

            assert_eq!(
                sumchecked_poly_monomial_form.len(),
                sumchecked_poly_evaluation_form.len()
            );
            eq_poly = fold_eq_poly(eq_poly, &folding_challenge, worker);
            assert_eq!(sumchecked_poly_evaluation_form.len(), eq_poly.len());
        }

        poly_size_log2 -= num_folding_steps;

        assert_eq!(sumchecked_poly_evaluation_form.len(), 1 << poly_size_log2);
        assert_eq!(sumchecked_poly_monomial_form.len(), 1 << poly_size_log2);
        assert_eq!(eq_poly.len(), 1 << poly_size_log2);

        #[cfg(feature = "gkr_self_checks")]
        {
            let full_sum = dot_product(&sumchecked_poly_evaluation_form, &eq_poly, worker);
            assert_eq!(full_sum, claim);
        }

        // query
        folding_challenges.push(folding_challenges_in_round.clone());

        let rs_oracle_to_query = {
            let lde_factor = whir_steps_lde_factors.next().unwrap();
            let rs = compute_column_major_lde_from_monomial_form(
                &sumchecked_poly_monomial_form,
                twiddles,
                lde_factor,
                Some(worker),
            );
            let next_folding_steps = *whir_steps_schedule.peek().unwrap();
            let next_oracle = commit_single_ext_poly::<F, E, T>(
                rs,
                1 << next_folding_steps,
                tree_cap_size,
                worker,
            );
            proof
                .intermediate_whir_oracles
                .push(WhirIntermediateCommitmentAndQueries {
                    commitment: WhirCommitment {
                        cap: next_oracle.tree.get_cap(),
                        _marker: core::marker::PhantomData,
                    },
                    queries: vec![],
                });
            core::mem::replace(&mut rs_oracle, next_oracle)
        };

        // draw OOD sample
        let ood_points: Vec<E> = draw_random_field_els(&mut transcript_seed, 1);
        let ood_point = ood_points[0];
        // compute OOD value
        let ood_value =
            evaluate_monomial_form(&sumchecked_poly_monomial_form[..], &ood_point, worker);
        #[cfg(feature = "gkr_self_checks")]
        {
            let pows = make_pows(
                ood_point,
                sumchecked_poly_evaluation_form.len().trailing_zeros() as usize,
            );
            let value = evaluate_multivariate(&sumchecked_poly_evaluation_form, &pows, worker);
            assert_eq!(value, ood_value);
        }

        proof.ood_samples.push(ood_value);

        let mut contributions_to_eq_poly = vec![];
        let mut contributions_to_eq_poly_with_base_points = vec![];

        let query_domain_size = 1u64 << query_domain_log2;

        let query_domain_generator = domain_generator_for_size::<F>(query_domain_size);
        let input_domain_size = 1u64 << rs_domain_log2;
        let extended_generator = domain_generator_for_size::<F>(input_domain_size);

        let set_generator = domain_generator_for_size::<F>(1u64 << num_folding_steps);
        let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<F, Global>(
            set_generator.inverse().unwrap(),
            1 << (num_folding_steps - 1),
        );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);

        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        let num_bits_for_queries = num_queries * query_index_bits;
        let (nonce, mut bit_source) =
            draw_query_bits(&mut transcript_seed, num_bits_for_queries, pow_bits, worker);
        proof.pow_nonces.push(nonce);

        let mut query_indexes = vec![];
        for _ in 0..num_queries {
            // query index is power for omega^k expression, where omega^{`input_domain_size`} == 1
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            query_indexes.push(query_index);
        }

        // and delinearization challenge
        let delinearization_challenges: Vec<E> = draw_random_field_els(&mut transcript_seed, 1);
        let delinearization_challenge = delinearization_challenges[0];
        delinearization_challenges_per_round.push(delinearization_challenge);

        // we will have OOD sample contribution
        contributions_to_eq_poly.push((ood_point, delinearization_challenge));

        let mut claim_correction = E::ZERO;
        {
            let mut t = ood_value;
            t.mul_assign(&delinearization_challenge);
            claim_correction.add_assign(&t);
        }
        let mut current_delinearization_challenge = delinearization_challenge;
        current_delinearization_challenge.square();
        for &query_index in query_indexes.iter() {
            assert!(query_index < query_domain_size as usize);
            let query_point = query_domain_generator.pow(query_index as u32);

            let base_root = extended_generator.pow(query_index as u32);
            assert_eq!(base_root.pow(1 << num_folding_steps), query_point);
            let base_root_inv = base_root.inverse().unwrap();
            for el in high_powers_offsets.iter() {
                let mut t = *el;
                t.mul_assign(&base_root_inv);
                debug_assert_eq!(
                    t.pow(1 << num_folding_steps),
                    query_point.inverse().unwrap()
                );
            }

            let (_coset_idx, evals, query) = rs_oracle_to_query.query_for_folded_index(query_index);
            let num_intermediate_oracles = proof.intermediate_whir_oracles.len();
            assert!(num_intermediate_oracles >= 2);
            let intermediate_oracle =
                &mut proof.intermediate_whir_oracles[num_intermediate_oracles - 2];
            intermediate_oracle.queries.push(query);

            let folded = fold_coset(
                evals,
                num_folding_steps,
                &folding_challenges_in_round,
                &base_root_inv,
                &high_powers_offsets,
                &two_inv,
            );

            query_references.push((query_index, query_point, folded));

            // and add into sumcheck claim
            contributions_to_eq_poly_with_base_points
                .push((query_point, delinearization_challenge));
            {
                let mut t = folded;
                t.mul_assign(&delinearization_challenge);
                claim_correction.add_assign(&t);
            }
            current_delinearization_challenge.mul_assign(&delinearization_challenge);
        }

        #[cfg(feature = "gkr_self_checks")]
        {
            let omega = domain_generator_for_size::<F>(query_domain_size);
            for (i, &query_index) in query_indexes.iter().enumerate() {
                let root = omega.pow(query_index as u32);
                let eval_from_monomial = evaluate_monomial_form(
                    &sumchecked_poly_monomial_form,
                    &E::from_base(root),
                    worker,
                );
                assert_eq!(
                    (query_index, root, eval_from_monomial),
                    query_references[i],
                    "diverged at query {}",
                    i
                );
                let pows = make_pows(
                    root,
                    sumchecked_poly_evaluation_form.len().trailing_zeros() as usize,
                );
                let eval_from_multivariate =
                    evaluate_multivariate_at_base(&sumchecked_poly_evaluation_form, &pows, worker);
                assert_eq!(eval_from_monomial, eval_from_multivariate);
            }
            query_references.clear();
        }
        #[cfg(not(feature = "gkr_self_checks"))]
        query_references.clear();

        // we now update the equality poly - initially we had eq(X, original_evalution_point), from which we folded few coordinates.
        // Now we should add more terms there to reflect OOD and in-domain samples
        update_eq_poly(
            eq_poly,
            &contributions_to_eq_poly,
            &contributions_to_eq_poly_with_base_points,
            worker,
        );

        // and remember new sumcheck claim
        claim.add_assign(&claim_correction);
    }

    // and final step is almost the same as the first one - we can fold few times, output evaluation form, and draw final query indexes,
    // check consistency between them, and perform final explicit sumcheck
    {
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let pow_bits = whir_pow_schedule.next().unwrap();
        assert!(num_folding_steps <= poly_size_log2);

        println!("Final round: fold by {}", 1 << num_folding_steps);

        let rs_domain_log2 = poly_size_log2 + (rs_oracle.cosets.len().trailing_zeros() as usize);
        let query_domain_log2 = rs_domain_log2 - num_folding_steps;

        // fold and send explicit form

        let mut folding_challenges_in_round = Vec::with_capacity(num_folding_steps);

        for folding_round in 0..num_folding_steps {
            let (f0, f1, f_half) = special_three_point_eval(
                &sumchecked_poly_evaluation_form[..],
                &eq_poly[..],
                worker,
            );
            let evaluation_point = E::from_base(two_inv);
            let univariate_coeffs = special_lagrange_interpolate(f0, f1, f_half, evaluation_point);
            // commit
            proof.sumcheck_polys.push(univariate_coeffs);
            commit_field_els(&mut transcript_seed, &univariate_coeffs);

            #[cfg(feature = "gkr_self_checks")]
            {
                let s0 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ZERO);
                assert_eq!(s0, f0);
                let s1 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ONE);
                assert_eq!(s1, f1);
                let s_half = evaluate_small_univariate_poly(&univariate_coeffs, &evaluation_point);
                assert_eq!(s_half, f_half);
                let mut v = s0;
                v.add_assign(&s1);
                assert_eq!(v, claim, "diverged at round {}", folding_round);
            }

            let folding_challenges = draw_random_field_els(&mut transcript_seed, 1);
            let folding_challenge = folding_challenges[0];
            folding_challenges_in_round.push(folding_challenge);

            let next_claim = evaluate_small_univariate_poly(&univariate_coeffs, &folding_challenge);
            claim = next_claim;
            // and fold the poly itself - both multivariate evals mapping, and monomial form

            fold_monomial_form(
                &mut sumchecked_poly_monomial_form,
                &mut monomial_form_buffer,
                &folding_challenge,
                worker,
            );

            sumchecked_poly_evaluation_form = fold_evaluation_form(
                &mut sumchecked_poly_evaluation_form[..],
                &folding_challenge,
                worker,
            );

            assert_eq!(
                sumchecked_poly_monomial_form.len(),
                sumchecked_poly_evaluation_form.len()
            );

            eq_poly = fold_eq_poly(eq_poly, &folding_challenge, worker);
            assert_eq!(sumchecked_poly_evaluation_form.len(), eq_poly.len());
        }

        poly_size_log2 -= num_folding_steps;

        assert_eq!(sumchecked_poly_evaluation_form.len(), 1 << poly_size_log2);
        assert_eq!(sumchecked_poly_monomial_form.len(), 1 << poly_size_log2);
        assert_eq!(eq_poly.len(), 1 << poly_size_log2);

        #[cfg(feature = "gkr_self_checks")]
        {
            let full_sum = dot_product(&sumchecked_poly_evaluation_form, &eq_poly, worker);
            assert_eq!(full_sum, claim);
        }

        // query

        let rs_oracle_to_query = rs_oracle;
        let query_domain_size = 1u64 << query_domain_log2;

        let query_domain_generator = domain_generator_for_size::<F>(query_domain_size);
        let input_domain_size = 1u64 << rs_domain_log2;
        let extended_generator = domain_generator_for_size::<F>(input_domain_size);

        let set_generator = domain_generator_for_size::<F>(1u64 << num_folding_steps);
        let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<F, Global>(
            set_generator.inverse().unwrap(),
            1 << (num_folding_steps - 1),
        );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);

        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        let num_bits_for_queries = num_queries * query_index_bits;
        let (nonce, mut bit_source) =
            draw_query_bits(&mut transcript_seed, num_bits_for_queries, pow_bits, worker);
        proof.pow_nonces.push(nonce);

        let mut query_indexes = vec![];
        for _ in 0..num_queries {
            // query index is power for omega^k expression, where omega^{`input_domain_size`} == 1
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            query_indexes.push(query_index);
        }

        for &query_index in query_indexes.iter() {
            assert!(query_index < query_domain_size as usize);
            let query_point = query_domain_generator.pow(query_index as u32);

            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();

            let (_coset_idx, evals, query) = rs_oracle_to_query.query_for_folded_index(query_index);
            let intermediate_oracle = proof.intermediate_whir_oracles.last_mut().unwrap();
            intermediate_oracle.queries.push(query);

            let folded = fold_coset(
                evals,
                num_folding_steps,
                &folding_challenges_in_round,
                &base_root_inv,
                &high_powers_offsets,
                &two_inv,
            );

            query_references.push((query_index, query_point, folded));
        }
        drop(rs_oracle_to_query);

        #[cfg(feature = "gkr_self_checks")]
        if sumchecked_poly_evaluation_form.len() > 1 {
            let omega = domain_generator_for_size::<F>(query_domain_size);
            for (i, &query_index) in query_indexes.iter().enumerate() {
                let root = omega.pow(query_index as u32);
                let eval_from_monomial = evaluate_monomial_form(
                    &sumchecked_poly_monomial_form,
                    &E::from_base(root),
                    worker,
                );
                assert_eq!(
                    (query_index, root, eval_from_monomial),
                    query_references[i],
                    "diverged at query {}",
                    i
                );
                let pows = make_pows(
                    root,
                    sumchecked_poly_evaluation_form.len().trailing_zeros() as usize,
                );
                let eval_from_multivariate =
                    evaluate_multivariate_at_base(&sumchecked_poly_evaluation_form, &pows, worker);
                assert_eq!(eval_from_monomial, eval_from_multivariate);
            }
            query_references.clear();
        }

        #[cfg(feature = "gkr_self_checks")]
        {
            let value = dot_product(&sumchecked_poly_evaluation_form[..], &eq_poly[..], worker);
            assert_eq!(value, claim);
        }
    }

    assert!(whir_steps_lde_factors.next().is_none());
    assert!(whir_steps_schedule.next().is_none());
    assert!(whir_queries_schedule.next().is_none());
    assert!(whir_pow_schedule.next().is_none());

    proof
}

fn commit_single_ext_poly<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    cosets: Vec<(Box<[E]>, F)>,
    values_per_leaf: usize,
    tree_cap_size: usize,
    worker: &Worker,
) -> ColumnMajorExtensionOracleForLDE<F, E, T>
where
    [(); E::DEGREE]: Sized,
{
    let mut t = Vec::with_capacity(cosets.len());
    let trace_len_log2 = cosets[0].0.len().trailing_zeros() as usize;
    for (column, offset) in cosets.into_iter() {
        assert!(column.len() > 0);
        let el = ColumnMajorExtensionOracleForCoset {
            values_normal_order: ColumnMajorCosetBoundTracePart {
                column: Arc::new(column),
                offset,
            },
        };
        t.push(el);
    }

    let source: Vec<_> = t
        .iter()
        .map(|el| vec![&el.values_normal_order.column[..]])
        .collect();
    let source_ref: Vec<_> = source.iter().map(|el| &el[..]).collect();

    let tree = T::construct_from_cosets::<E, Global>(
        &source_ref[..],
        values_per_leaf,
        tree_cap_size,
        true,
        true,
        false,
        worker,
    );

    ColumnMajorExtensionOracleForLDE {
        cosets: t,
        tree,
        values_per_leaf,
        trace_len_log2,
    }
}

fn fold_monomial_form<E: Field>(
    input: &mut Vec<E>,
    buffer: &mut Vec<E>,
    challenge: &E,
    worker: &Worker,
) {
    assert!(input.len().is_power_of_two());
    assert!(buffer.capacity() >= input.len() / 2);
    assert!(buffer.is_empty());

    let work_size = input.len() / 2;
    if work_size == 0 {
        return;
    }

    let input_pairs = input.as_chunks::<2>().0;
    let dst_uninit = &mut buffer.spare_capacity_mut()[..work_size];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        input_pairs
            .chunks_for_geometry(geometry)
            .enumerate()
            .zip(dst_uninit.chunks_for_geometry_mut(geometry))
            .for_each(|((idx, src_chunk), dst_chunk)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    for ([c0, c1], d) in src_chunk.iter().zip(dst_chunk.iter_mut()) {
                        let mut result = *c1;
                        result.mul_assign(challenge);
                        result.add_assign(c0);
                        d.write(result);
                    }
                });
            })
    });

    unsafe {
        buffer.set_len(work_size);
    }

    core::mem::swap(input, buffer);
    buffer.clear();
}

#[cfg(test)]
fn fold_monomial_form_serial<E: Field>(input: &mut Vec<E>, buffer: &mut Vec<E>, challenge: &E) {
    assert!(input.len().is_power_of_two());
    assert!(buffer.capacity() >= input.len() / 2);
    assert!(buffer.is_empty());

    for ([c0, c1], dst) in input
        .as_chunks::<2>()
        .0
        .iter()
        .zip(buffer.spare_capacity_mut()[..input.len() / 2].iter_mut())
    {
        let mut result = *c1;
        result.mul_assign(challenge);
        result.add_assign(c0);
        dst.write(result);
    }
    unsafe {
        buffer.set_len(input.len() / 2);
    }

    core::mem::swap(input, buffer);
    buffer.clear();
}

#[cfg(test)]
fn fold_evaluation_form_serial<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    input: &'a mut [E],
    challenge: &E,
) -> &'a mut [E] {
    assert!(input.len().is_power_of_two());
    let half_len = input.len() / 2;
    let f1_coeff = *challenge;

    let (first_half, second_half) = input.split_at_mut(half_len);
    for (a, b) in first_half.iter_mut().zip(second_half.iter()) {
        let mut t = *b;
        t.sub_assign(a);
        t.mul_assign(&f1_coeff);
        a.add_assign(&t);
    }

    first_half
}

fn fold_evaluation_form<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    input: &'a mut [E],
    challenge: &E,
    worker: &Worker,
) -> &'a mut [E] {
    assert!(input.len().is_power_of_two());
    let half_len = input.len() / 2;
    if half_len == 0 {
        return &mut input[..0];
    }

    let f1_coeff = *challenge;

    let (first_half, second_half) = input.split_at_mut(half_len);

    worker.scope_with_threshold(half_len, PAR_THRESHOLD, |scope, geometry| {
        first_half
            .chunks_for_geometry_mut(geometry)
            .enumerate()
            .zip(second_half.chunks_for_geometry(geometry))
            .for_each(|((idx, dst), src)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    for (a, b) in dst.iter_mut().zip(src.iter()) {
                        let mut t = *b;
                        t.sub_assign(a);
                        t.mul_assign(&f1_coeff);
                        a.add_assign(&t);
                    }
                });
            })
    });

    first_half
}

#[cfg(test)]
fn fold_eq_poly_serial<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    eq_poly: &'a mut [E],
    challenge: &E,
) -> &'a mut [E] {
    assert!(eq_poly.len().is_power_of_two());
    assert!(eq_poly.len() >= 2);
    let half_len = eq_poly.len() / 2;
    let f1_coeff = *challenge;

    let (first_half, second_half) = eq_poly.split_at_mut(half_len);
    for (a, b) in first_half.iter_mut().zip(second_half.iter()) {
        let mut t = *b;
        t.sub_assign(a);
        t.mul_assign(&f1_coeff);
        a.add_assign(&t);
    }

    first_half
}

fn fold_eq_poly<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    eq_poly: &'a mut [E],
    challenge: &E,
    worker: &Worker,
) -> &'a mut [E] {
    assert!(eq_poly.len().is_power_of_two());
    assert!(eq_poly.len() >= 2);
    let half_len = eq_poly.len() / 2;

    let f1_coeff = *challenge;

    let (first_half, second_half) = eq_poly.split_at_mut(half_len);

    worker.scope_with_threshold(half_len, PAR_THRESHOLD, |scope, geometry| {
        first_half
            .chunks_for_geometry_mut(geometry)
            .enumerate()
            .zip(second_half.chunks_for_geometry(geometry))
            .for_each(|((idx, dst), src)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    for (a, b) in dst.iter_mut().zip(src.iter()) {
                        let mut t = *b;
                        t.sub_assign(a);
                        t.mul_assign(&f1_coeff);
                        a.add_assign(&t);
                    }
                });
            })
    });

    first_half
}

#[cfg(test)]
fn dot_product_serial<F: PrimeField, E: FieldExtension<F> + Field>(a: &[E], b: &[E]) -> E {
    assert!(a.len() > 0);
    assert_eq!(a.len(), b.len());
    let mut result = E::ZERO;
    for (a, b) in a.iter().zip(b.iter()) {
        let mut t = *a;
        t.mul_assign(b);
        result.add_assign(&t);
    }
    result
}

fn dot_product<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    worker: &Worker,
) -> E {
    assert!(a.len() > 0);
    assert_eq!(a.len(), b.len());

    let geometry = worker.get_geometry_with_threshold(a.len(), PAR_THRESHOLD);
    let mut partial_results = vec![E::ZERO; geometry.len()];

    worker.scope_with_threshold(a.len(), PAR_THRESHOLD, |scope, geometry| {
        a.chunks_for_geometry(geometry)
            .enumerate()
            .zip(b.chunks_for_geometry(geometry))
            .zip(partial_results.iter_mut())
            .for_each(|(((idx, a_chunk), b_chunk), partial)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    let mut acc = E::ZERO;
                    for (a, b) in a_chunk.iter().zip(b_chunk.iter()) {
                        let mut t = *a;
                        t.mul_assign(b);
                        acc.add_assign(&t);
                    }
                    *partial = acc;
                });
            });
    });

    partial_results.iter().fold(E::ZERO, |mut acc, p| {
        acc.add_assign(p);
        acc
    })
}

// Accumulate partial [f0, f1, f_half] sums over aligned quadruples of slice elements.
// a_low[i] = a[i], a_high[i] = a[i + half], same for b.  quart scaling is NOT applied here.
#[inline(always)]
fn three_point_partial<E: Field>(a_low: &[E], a_high: &[E], b_low: &[E], b_high: &[E]) -> [E; 3] {
    let mut f0 = E::ZERO;
    let mut f1 = E::ZERO;
    let mut f_half = E::ZERO;
    for ((a0, a1), (b0, b1)) in a_low
        .iter()
        .zip(a_high.iter())
        .zip(b_low.iter().zip(b_high.iter()))
    {
        let mut t0 = *a0;
        t0.mul_assign(b0);
        f0.add_assign(&t0);

        let mut t1 = *a1;
        t1.mul_assign(b1);
        f1.add_assign(&t1);

        let mut tt = *a1;
        tt.add_assign(a0);
        let mut t_half = *b1;
        t_half.add_assign(b0);
        t_half.mul_assign(&tt);
        f_half.add_assign(&t_half);
    }
    [f0, f1, f_half]
}

#[cfg(test)]
fn special_three_point_eval_serial<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
) -> (E, E, E) {
    assert!(a.len() > 0);
    assert_eq!(a.len(), b.len());
    let quart = F::from_u32_unchecked(4).inverse().unwrap();
    let half = a.len() / 2;
    let (a_low, a_high) = a.split_at(half);
    let (b_low, b_high) = b.split_at(half);
    let [f0, f1, mut f_half] = three_point_partial(a_low, a_high, b_low, b_high);
    f_half.mul_assign_by_base(&quart);
    (f0, f1, f_half)
}

fn special_three_point_eval<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    worker: &Worker,
) -> (E, E, E) {
    assert!(a.len() > 0);
    assert_eq!(a.len(), b.len());

    let quart = F::from_u32_unchecked(4).inverse().unwrap();
    let half = a.len() / 2;
    let (a_low, a_high) = a.split_at(half);
    let (b_low, b_high) = b.split_at(half);

    // Each thread accumulates partial [f0, f1, f_half] over its chunk of pairs,
    // then we reduce across threads.  When half < PAR_THRESHOLD the geometry has
    // one chunk and smart_spawn runs on the calling thread.
    let mut partial_results = vec![
        [E::ZERO; 3];
        worker
            .get_geometry_with_threshold(half, PAR_THRESHOLD)
            .len()
    ];

    let [f0, f1, mut f_half] = {
        worker.scope_with_threshold(half, PAR_THRESHOLD, |scope, geometry| {
            a_low
                .chunks_for_geometry(geometry)
                .enumerate()
                .zip(
                    a_high
                        .chunks_for_geometry(geometry)
                        .zip(b_low.chunks_for_geometry(geometry))
                        .zip(b_high.chunks_for_geometry(geometry)),
                )
                .zip(partial_results.iter_mut())
                .for_each(|(((idx, al), ((ah, bl), bh)), partial)| {
                    Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                        *partial = three_point_partial(al, ah, bl, bh);
                    });
                });
        });

        partial_results
            .iter()
            .fold([E::ZERO; 3], |mut acc, partial| {
                acc[0].add_assign(&partial[0]);
                acc[1].add_assign(&partial[1]);
                acc[2].add_assign(&partial[2]);
                acc
            })
    };

    // quart scaling is applied once after the full reduction, not per-thread
    f_half.mul_assign_by_base(&quart);
    (f0, f1, f_half)
}

#[cfg(test)]
fn evaluate_monomial_form_serial<E: Field>(coeffs: &[E], point: &E) -> E {
    let mut result = E::ZERO;
    let mut c = E::ONE;
    for a in coeffs.iter() {
        let mut t = *a;
        t.mul_assign(&c);
        c.mul_assign(point);
        result.add_assign(&t);
    }
    result
}

fn evaluate_monomial_form<E: Field>(coeffs: &[E], point: &E, worker: &Worker) -> E {
    if coeffs.is_empty() {
        return E::ZERO;
    }

    let geometry = worker.get_geometry_with_threshold(coeffs.len(), PAR_THRESHOLD);
    let num_chunks = geometry.len();
    let chunk_size = geometry.ordinary_chunk_size;

    // point^chunk_size via binary exponentiation
    let chunk_power = {
        let mut result = E::ONE;
        let mut base = *point;
        let mut exp = chunk_size;
        while exp > 0 {
            if exp & 1 == 1 {
                result.mul_assign(&base);
            }
            base.square();
            exp >>= 1;
        }
        result
    };

    // offset_powers[j] = point^(j * chunk_size) = chunk_power^j
    let mut offset_powers = Vec::with_capacity(num_chunks);
    let mut current = E::ONE;
    for _ in 0..num_chunks {
        offset_powers.push(current);
        current.mul_assign(&chunk_power);
    }

    let mut partial_results = vec![E::ZERO; num_chunks];

    worker.scope_with_threshold(coeffs.len(), PAR_THRESHOLD, |scope, geometry| {
        coeffs
            .chunks_for_geometry(geometry)
            .enumerate()
            .zip(partial_results.iter_mut())
            .for_each(|((idx, chunk), partial)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    // Horner within chunk, starting at relative power point^0
                    let mut acc = E::ZERO;
                    let mut c = E::ONE;
                    for a in chunk.iter() {
                        let mut t = *a;
                        t.mul_assign(&c);
                        c.mul_assign(point);
                        acc.add_assign(&t);
                    }
                    *partial = acc;
                });
            });
    });

    // result = sum_j offset_powers[j] * partial_results[j]
    let mut result = E::ZERO;
    for (offset, partial) in offset_powers.iter().zip(partial_results.iter()) {
        let mut t = *partial;
        t.mul_assign(offset);
        result.add_assign(&t);
    }
    result
}

fn special_lagrange_interpolate<E: Field>(
    eval_at_0: E,
    eval_at_1: E,
    eval_at_random: E,
    random_point: E,
) -> [E; 3] {
    // easier to compute special case than generic
    let mut coeffs_for_0 = [E::ZERO, E::ZERO, E::ONE];
    coeffs_for_0[1] = E::ONE;
    coeffs_for_0[1].add_assign(&random_point);
    coeffs_for_0[1].negate();

    coeffs_for_0[0] = E::ONE;
    coeffs_for_0[0].mul_assign(&random_point);

    let mut coeffs_for_1 = [E::ZERO, E::ZERO, E::ONE];
    coeffs_for_1[1] = E::ZERO;
    coeffs_for_1[1].add_assign(&random_point);
    coeffs_for_1[1].negate();

    coeffs_for_1[0] = E::ZERO;
    coeffs_for_1[0].mul_assign(&random_point);

    let mut coeffs_for_random_point = [E::ZERO, E::ZERO, E::ONE];
    coeffs_for_random_point[1] = E::ZERO;
    coeffs_for_random_point[1].add_assign(&E::ONE);
    coeffs_for_random_point[1].negate();

    coeffs_for_random_point[0] = E::ZERO;
    coeffs_for_random_point[0].mul_assign(&E::ONE);

    let mut dens = [E::ONE, E::ONE, E::ONE];

    let mut t = E::ZERO;
    t.sub_assign(&E::ONE);
    dens[0].mul_assign(&t);
    let mut t = E::ZERO;
    t.sub_assign(&random_point);
    dens[0].mul_assign(&t);

    let mut t = E::ONE;
    t.sub_assign(&E::ZERO);
    dens[1].mul_assign(&t);
    let mut t = E::ONE;
    t.sub_assign(&random_point);
    dens[1].mul_assign(&t);

    let mut t = random_point;
    t.sub_assign(&E::ZERO);
    dens[2].mul_assign(&t);
    let mut t = random_point;
    t.sub_assign(&E::ONE);
    dens[2].mul_assign(&t);

    let mut buffer = [E::ZERO; 3];
    batch_inverse_inplace(&mut dens, &mut buffer);

    let mut result = [E::ZERO; 3];
    for (eval, den, coeffs) in [
        (eval_at_0, dens[0], coeffs_for_0),
        (eval_at_1, dens[1], coeffs_for_1),
        (eval_at_random, dens[2], coeffs_for_random_point),
    ]
    .into_iter()
    {
        for (i, c) in coeffs.into_iter().enumerate() {
            let mut t = c;
            t.mul_assign(&den);
            t.mul_assign(&eval);
            result[i].add_assign(&t);
        }
    }

    result
}

fn make_pows<E: Field>(el: E, num_powers: usize) -> Vec<E> {
    let mut result = Vec::with_capacity(num_powers);
    let mut current = el;
    for _ in 0..num_powers {
        result.push(current);
        current.square();
    }

    result
}

fn update_eq_poly<F: PrimeField, E: FieldExtension<F> + Field>(
    eq_poly: &mut [E],
    ood_samples: &[(E, E)],
    in_domain_samples: &[(F, E)],
    worker: &Worker,
) {
    assert!(eq_poly.len().is_power_of_two());
    assert_eq!(ood_samples.len(), 1);
    for (point, challenge) in ood_samples.iter() {
        let pows = make_pows(*point, eq_poly.len().trailing_zeros() as usize);
        let eq_polys = make_eq_poly_in_full::<E>(&pows, worker);
        for (dst, src) in eq_poly.iter_mut().zip(eq_polys.last().unwrap().iter()) {
            let mut t = *challenge;
            t.mul_assign(src);
            dst.add_assign(&t);
        }
    }
    for (point, challenge) in in_domain_samples.iter() {
        let pows = make_pows(*point, eq_poly.len().trailing_zeros() as usize);
        let eq_polys = make_eq_poly_in_full::<F>(&pows, worker);
        for (dst, src) in eq_poly.iter_mut().zip(eq_polys.last().unwrap().iter()) {
            let mut t = *challenge;
            t.mul_assign_by_base(src);
            dst.add_assign(&t);
        }
    }
}

fn evaluate_base_multivariate<F: PrimeField, E: FieldExtension<F> + Field>(
    evals: &[F],
    point: &[E],
    worker: &Worker,
) -> E {
    let mut eqs = make_eq_poly_in_full::<E>(point, worker);
    let eq = eqs.pop().unwrap();
    assert_eq!(eq.len(), evals.len());
    let mut result = E::ZERO;
    for (a, b) in eq.iter().zip(evals.iter()) {
        let mut t = *a;
        t.mul_assign_by_base(b);
        result.add_assign(&t);
    }
    result
}

fn evaluate_multivariate<E: Field>(evals: &[E], point: &[E], worker: &Worker) -> E {
    let mut eqs = make_eq_poly_in_full::<E>(point, worker);
    let eq = eqs.pop().unwrap();
    assert_eq!(eq.len(), evals.len());
    let mut result = E::ZERO;
    for (a, b) in eq.iter().zip(evals.iter()) {
        let mut t = *a;
        t.mul_assign(b);
        result.add_assign(&t);
    }
    result
}

fn evaluate_multivariate_at_base<F: PrimeField, E: FieldExtension<F> + Field>(
    evals: &[E],
    point: &[F],
    worker: &Worker,
) -> E {
    let mut eqs = make_eq_poly_in_full::<F>(point, worker);
    let eq = eqs.pop().unwrap();
    assert_eq!(eq.len(), evals.len());
    let mut result = E::ZERO;
    for (a, b) in eq.iter().zip(evals.iter()) {
        let mut t = *b;
        t.mul_assign_by_base(a);
        result.add_assign(&t);
    }
    result
}

fn evaluate_multivariate_at_base_for_domain_hypercube<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
>(
    evals: &[E],
    point: &[F],
) -> E {
    let mut eqs = make_domain_eq_poly_in_full::<F, F>(point);
    let eq = eqs.pop().unwrap();
    assert_eq!(eq.len(), evals.len());
    let mut result = E::ZERO;
    for (a, b) in eq.iter().zip(evals.iter()) {
        let mut t = *b;
        t.mul_assign_by_base(a);
        result.add_assign(&t);
    }
    result
}

fn fold_coset<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    mut flattened_evals: Vec<E>,
    num_folding_rounds: usize,
    folding_challenges: &[E],
    base_root_inv: &F,
    high_powers_offsets: &[F],
    two_inv: &F,
) -> E {
    assert_eq!(num_folding_rounds, folding_challenges.len());
    debug_assert_eq!(high_powers_offsets[0], F::ONE);
    let mut root_inv = *base_root_inv;
    // Now we can fold queries values, in a normal FRI style
    let mut buffer = Vec::with_capacity(flattened_evals.len());
    for folding_step in 0..num_folding_rounds {
        let (src, dst) = if folding_step % 2 == 0 {
            (&flattened_evals[..], &mut buffer)
        } else {
            (&buffer[..], &mut flattened_evals)
        };
        assert!(dst.is_empty());
        assert!(src.is_empty() == false);
        assert!(src.len().is_power_of_two());
        assert_eq!(src.len(), 1 << (num_folding_rounds - folding_step));
        let folding_challenge = folding_challenges[folding_step];
        for (set_idx, [a, b]) in src.as_chunks::<2>().0.iter().enumerate() {
            let mut t = *a;
            t.sub_assign(b);
            t.mul_assign(&folding_challenge);

            let mut root = root_inv;
            root.mul_assign(&high_powers_offsets[set_idx]);

            t.mul_assign_by_base(&root);

            t.add_assign(a);
            t.add_assign(b);
            t.mul_assign_by_base(two_inv);
            dst.push(t);
        }
        if folding_step % 2 == 0 {
            flattened_evals.clear();
        } else {
            buffer.clear();
        };
        root_inv.square();
    }

    let folded = if num_folding_rounds % 2 == 1 {
        &buffer[..]
    } else {
        &flattened_evals[..]
    };
    assert_eq!(folded.len(), 1);

    folded[0]
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4},
        merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap,
    };
    use field::FieldExtension;
    use rand::{rngs::ThreadRng, RngCore};

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn random_e(rng: &mut ThreadRng) -> E
    where
        [(); <E as FieldExtension<F>>::DEGREE]: Sized,
    {
        let coefs = [(); <E as FieldExtension<F>>::DEGREE]
            .map(|_| F::from_u32_with_reduction(rng.next_u32()));

        <E as FieldExtension<F>>::from_coeffs(coefs)
    }

    #[test]
    fn test_fold_monomial_form() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let input: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let challenge = random_e(&mut rng);

        let mut input_ser = input.clone();
        let mut buffer_ser: Vec<E> = Vec::with_capacity(size / 2);
        fold_monomial_form_serial(&mut input_ser, &mut buffer_ser, &challenge);

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let mut input_par = input.clone();
            let mut buffer_par: Vec<E> = Vec::with_capacity(size / 2);
            fold_monomial_form(&mut input_par, &mut buffer_par, &challenge, &worker);
            assert_eq!(
                input_par, input_ser,
                "fold_monomial_form mismatch with {} threads",
                num_threads
            );
        }
    }

    // fn make_base_oracle(
    //     size: usize,
    //     worker: &Worker,
    // ) -> ColumnMajorBaseOracleForLDE<F, Blake2sU32MerkleTreeWithCap> {
    //     let main_domain: Vec<F> = (1..=size).map(|el| {
    //         F::from_u32_unchecked(el as u32)
    //     }).collect();
    //     let twiddles = Twiddles::<F, Global>::new(size, worker);
    //     let main_domain = Arc::new(main_domain.into_boxed_slice());

    //     let other_domains =
    //         compute_column_major_lde_from_main_domain(main_domain.clone(), &twiddles, 2);
    //     let original_values_normal_order = ColumnMajorCosetBoundTracePart {
    //         column: main_domain,
    //         offset: F::ONE,
    //     };
    //     let source = Some(original_values_normal_order)
    //         .into_iter()
    //         .chain(other_domains.into_iter());

    //     let mut result = ColumnMajorBaseOracleForLDE { cosets: vec![] };
    //     for coset in source {
    //         let el = ColumnMajorBaseOracleForCoset {
    //             original_values_normal_order: vec![coset],
    //             tree: <Blake2sU32MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<F>>::dummy(),
    //             values_per_leaf: 2,
    //             trace_len_log2: size.trailing_zeros() as usize,
    //         };
    //         result.cosets.push(el);
    //     }

    //     result
    // }

    fn make_base_oracle(
        size: usize,
        worker: &Worker,
        offset: usize,
    ) -> (
        ColumnMajorBaseOracleForLDE<F, Blake2sU32MerkleTreeWithCap>,
        Vec<F>,
    ) {
        todo!();

        // let coeffs: Vec<F> = (1..=size)
        //     .map(|el| F::from_u32_with_reduction((el + offset) as u32))
        //     .collect();
        // let twiddles = Twiddles::<F, Global>::new(size, worker);

        // let cosets = compute_column_major_lde_from_monomial_form(&coeffs, &twiddles, 2);

        // let mut result = ColumnMajorBaseOracleForLDE { cosets: vec![] };
        // for (column, offset) in cosets.into_iter() {
        //     let tree = <Blake2sU32MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<F>>::construct_for_column_major_coset::<F, Global>(
        //         &[&column[..]],
        //         2,
        //         1,
        //         true,
        //         false,
        //         worker
        //     );
        //     let el = ColumnMajorBaseOracleForCoset {
        //         original_values_normal_order: vec![ColumnMajorCosetBoundTracePart {
        //             column: Arc::new(column),
        //             offset,
        //         }],
        //         tree,
        //         values_per_leaf: 2,
        //         trace_len_log2: size.trailing_zeros() as usize,
        //     };
        //     result.cosets.push(el);
        // }

        // (result, coeffs)
    }

    #[test]
    fn test_fold_evaluation_form() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let input: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let challenge = random_e(&mut rng);

        let mut input_ser = input.clone();
        let expected = fold_evaluation_form_serial::<F, E>(&mut input_ser, &challenge);
        let expected = expected.to_vec();

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let mut input_par = input.clone();
            let got = fold_evaluation_form::<F, E>(&mut input_par, &challenge, &worker);
            assert_eq!(
                got,
                expected.as_slice(),
                "fold_evaluation_form mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn test_fold_eq_poly() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let eq: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let challenge = random_e(&mut rng);

        let mut eq_ser = eq.clone();
        let expected = fold_eq_poly_serial::<F, E>(&mut eq_ser, &challenge);
        let expected = expected.to_vec();

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let mut eq_par = eq.clone();
            let got = fold_eq_poly::<F, E>(&mut eq_par, &challenge, &worker);
            assert_eq!(
                got,
                expected.as_slice(),
                "fold_eq_poly mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn test_special_three_point_eval() {
        let mut rng = rand::rng();
        let size = 1 << 12;
        let a: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let b: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();

        let (e_f0, e_f1, e_fh) = special_three_point_eval_serial::<F, E>(&a, &b);

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let (f0, f1, fh) = special_three_point_eval::<F, E>(&a, &b, &worker);
            assert_eq!(
                (f0, f1, fh),
                (e_f0, e_f1, e_fh),
                "special_three_point_eval mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn test_dot_product() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let a: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let b: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();

        let expected = dot_product_serial::<F, E>(&a, &b);

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let got = dot_product::<F, E>(&a, &b, &worker);
            assert_eq!(
                got, expected,
                "dot_product mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn test_evaluate_monomial_form() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let coeffs: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let point = random_e(&mut rng);

        let expected = evaluate_monomial_form_serial(&coeffs, &point);

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let got = evaluate_monomial_form(&coeffs, &point, &worker);
            assert_eq!(
                got, expected,
                "evaluate_monomial_form mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn test_special_three_point_eval_correctness() {
        let mut rng = rand::rng();
        let worker = Worker::new_with_num_threads(8);
        let quart_inv = F::from_u32_unchecked(4).inverse().unwrap();

        for size_log2 in [3u32, 13] {
            let size = 1 << size_log2;
            let a: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
            let b: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
            let half = size / 2;

            // f(0) = dot(a[0..half], b[0..half])
            let expected_f0 = (0..half).fold(E::ZERO, |mut acc, i| {
                let mut t = a[i];
                t.mul_assign(&b[i]);
                acc.add_assign(&t);
                acc
            });
            // f(1) = dot(a[half..], b[half..])
            let expected_f1 = (0..half).fold(E::ZERO, |mut acc, i| {
                let mut t = a[i + half];
                t.mul_assign(&b[i + half]);
                acc.add_assign(&t);
                acc
            });
            // f(1/2) = 1/4 * sum_i (a[i]+a[i+half]) * (b[i]+b[i+half])
            let mut expected_fh = (0..half).fold(E::ZERO, |mut acc, i| {
                let mut ta = a[i];
                ta.add_assign(&a[i + half]);
                let mut tb = b[i];
                tb.add_assign(&b[i + half]);
                ta.mul_assign(&tb);
                acc.add_assign(&ta);
                acc
            });
            expected_fh.mul_assign_by_base(&quart_inv);

            let full_dot = (0..size).fold(E::ZERO, |mut acc, i| {
                let mut t = a[i];
                t.mul_assign(&b[i]);
                acc.add_assign(&t);
                acc
            });
            let mut f0_plus_f1 = expected_f0;
            f0_plus_f1.add_assign(&expected_f1);
            assert_eq!(f0_plus_f1, full_dot, "sanity: f(0)+f(1) == dot(a,b)");

            let (f0, f1, fh) = special_three_point_eval::<F, E>(&a, &b, &worker);
            assert_eq!(f0, expected_f0, "f(0) wrong at size 2^{}", size_log2);
            assert_eq!(f1, expected_f1, "f(1) wrong at size 2^{}", size_log2);
            assert_eq!(fh, expected_fh, "f(1/2) wrong at size 2^{}", size_log2);
        }
    }
    #[test]
    fn test_evaluate_monomial_form_correctness() {
        let mut rng = rand::rng();
        let worker = Worker::new_with_num_threads(8);

        // f(x) = 3 + 5x  at  x = 2  →  3 + 10 = 13
        {
            let c0 = E::from_base(F::from_u32_unchecked(3));
            let c1 = E::from_base(F::from_u32_unchecked(5));
            let x = E::from_base(F::from_u32_unchecked(2));
            let mut expected = c1;
            expected.mul_assign(&x);
            expected.add_assign(&c0);
            assert_eq!(evaluate_monomial_form(&[c0, c1], &x, &worker), expected);
        }

        {
            let n = 2048usize;
            let p = E::from_base(F::from_u32_unchecked(3));
            let mut coeffs = vec![E::ZERO; n];
            *coeffs.last_mut().unwrap() = E::ONE;
            let expected = (0..n - 1).fold(E::ONE, |mut acc, _| {
                acc.mul_assign(&p);
                acc
            });
            assert_eq!(evaluate_monomial_form(&coeffs, &p, &worker), expected);
        }

        for size_log2 in [3u32, 13] {
            let size = 1 << size_log2;
            let coeffs: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
            let p = random_e(&mut rng);

            let expected = {
                let mut acc = E::ZERO;
                let mut pow = E::ONE;
                for c in coeffs.iter() {
                    let mut t = *c;
                    t.mul_assign(&pow);
                    acc.add_assign(&t);
                    pow.mul_assign(&p);
                }
                acc
            };

            let got = evaluate_monomial_form(&coeffs, &p, &worker);
            assert_eq!(
                got, expected,
                "evaluate_monomial_form wrong at size 2^{}",
                size_log2
            );
        }
    }

    #[test]
    fn test_domain_hypercube_evals() {
        let worker = Worker::new_with_num_threads(1);
        let size: usize = 4;

        let main_domain: Vec<F> = (1..=size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        dbg!(&main_domain);

        let root = domain_generator_for_size::<F>(size as u64);
        let domain = materialize_powers_serial_starting_with_one::<F, Global>(root, size);
        dbg!(&domain);
        for i in 0..size {
            dbg!(i);
            let domain_point = root.pow(i as u32);
            let pows = make_pows(domain_point, size.trailing_zeros() as usize);
            dbg!(&pows);
            let value = evaluate_multivariate_at_base_for_domain_hypercube(&main_domain, &pows);
            dbg!(value);
        }
    }

    #[test]
    fn test_whir() {
        let worker = Worker::new_with_num_threads(1);
        let size = 128;

        let mut inputs = vec![];
        let mut monomial_forms = vec![];
        for i in 0..3 {
            let (input, monomial) = make_base_oracle(size, &worker, i * 32);
            inputs.push(input);
            monomial_forms.push(monomial);
        }

        let [mem, wit, setup] = inputs.try_into().unwrap();

        let original_evaluation_point: Vec<_> = (0..size.trailing_zeros())
            .map(|el| E::from_base(F::from_u32_unchecked(4 << el)))
            .collect();
        let twiddles = Twiddles::<F, Global>::new(size, &worker);

        let original_claims: Vec<_> = monomial_forms
            .iter()
            .map(|el| {
                // compute on hypercube
                let mut t = el.to_vec();
                bitreverse_enumeration_inplace(&mut t);
                multivariate_coeffs_into_hypercube_evals(&mut t, size.trailing_zeros());
                let eval = evaluate_base_multivariate(&t, &original_evaluation_point, &worker);

                vec![eval]
            })
            .collect::<Vec<_>>();

        let [a, b, c] = original_claims.try_into().unwrap();

        let proof = whir_fold(
            mem,
            a,
            wit,
            b,
            &setup,
            c,
            original_evaluation_point,
            2,
            E::from_base(F::from_u32_with_reduction(7)),
            vec![1, 2, 3],
            vec![4, 4, 4],
            vec![8, 16],
            vec![10, 10, 10],
            &twiddles,
            Seed::default(),
            1,
            size.trailing_zeros() as usize,
            &worker,
        );
    }
}
