use super::*;
use std::collections::BTreeMap;

use crate::gkr::sumcheck::access_and_fold::GKRStorage;
use crate::gkr::sumcheck::eq_poly::{
    evaluate_constant_and_quadratic_coeffs_with_precomputed_eq, make_eq_poly_in_full,
};
use crate::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchedGKRKernel, ExtensionCopyGKRRelation, GKRInputs,
    LookupBaseMinusMultiplicityByBaseGKRRelation, LookupBasePairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
use crate::gkr::sumcheck::{
    evaluate_eq_poly, evaluate_small_univariate_poly, output_univariate_monomial_form_max_quadratic,
};
use crate::worker::Worker;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRLayerDescription, NoFieldGKRRelation};

pub enum KernelVariant<F: PrimeField, E: FieldExtension<F> + Field> {
    BaseCopy(BaseFieldCopyGKRRelation),
    ExtCopy(ExtensionCopyGKRRelation),
    Product(SameSizeProductGKRRelation),
    MaskIdentity(MaskIntoIdentityProductGKRRelation),
    LookupPair(LookupPairGKRRelation),
    LookupBasePair(LookupBasePairGKRRelation<F, E>),
    LookupBaseMinusMultiplicity(LookupBaseMinusMultiplicityByBaseGKRRelation<F, E>),
    LookupUnbalanced(LookupRationalPairWithUnbalancedBaseGKRRelation<F, E>),
}

macro_rules! dispatch_kernel {
    ($self:expr, |$k:ident| $body:expr) => {
        match $self {
            KernelVariant::BaseCopy(ref $k) => $body,
            KernelVariant::ExtCopy(ref $k) => $body,
            KernelVariant::Product(ref $k) => $body,
            KernelVariant::MaskIdentity(ref $k) => $body,
            KernelVariant::LookupPair(ref $k) => $body,
            KernelVariant::LookupBasePair(ref $k) => $body,
            KernelVariant::LookupBaseMinusMultiplicity(ref $k) => $body,
            KernelVariant::LookupUnbalanced(ref $k) => $body,
        }
    };
}

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelVariant<F, E> {
    pub fn num_challenges(&self) -> usize {
        dispatch_kernel!(self, |k| BatchedGKRKernel::<F, E>::num_challenges(k))
    }

    pub fn evaluate_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        step: usize,
        batch_challenges: &[E],
        folding_challenges: &[E],
        accumulator: &mut [[E; 2]],
        total_sumcheck_rounds: usize,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
        worker: &Worker,
    ) {
        dispatch_kernel!(self, |k| k.evaluate_over_storage(
            storage,
            step,
            batch_challenges,
            folding_challenges,
            accumulator,
            total_sumcheck_rounds,
            last_evaluations,
            worker,
        ))
    }

    pub fn get_inputs(&self) -> GKRInputs {
        dispatch_kernel!(self, |k| BatchedGKRKernel::<F, E>::get_inputs(k))
    }
}

struct KernelCollector<F: PrimeField, E: FieldExtension<F> + Field> {
    kernels: Vec<KernelVariant<F, E>>,
    batch_challenges_per_kernel: Vec<Vec<E>>,
    kernel_outputs: Vec<Vec<GKRAddress>>,
    current_batch_challenge: E,
    batch_challenge_base: E,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    fn new(batch_challenge_base: E) -> Self {
        Self {
            kernels: Vec::new(),
            batch_challenges_per_kernel: Vec::new(),
            kernel_outputs: Vec::new(),
            current_batch_challenge: E::ONE,
            batch_challenge_base,
        }
    }

    fn register(&mut self, kernel: KernelVariant<F, E>) {
        let num_challenges = kernel.num_challenges();
        let challenges: Vec<E> = (0..num_challenges)
            .map(|_| {
                let c = self.current_batch_challenge;
                self.current_batch_challenge
                    .mul_assign(&self.batch_challenge_base);
                c
            })
            .collect();
        self.kernel_outputs
            .push(kernel.get_inputs().outputs_in_extension);
        self.kernels.push(kernel);
        self.batch_challenges_per_kernel.push(challenges);
    }

    fn is_empty(&self) -> bool {
        self.kernels.is_empty()
    }

    fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        let mut combined = E::ZERO;
        for (challenges, outputs) in self
            .batch_challenges_per_kernel
            .iter()
            .zip(self.kernel_outputs.iter())
        {
            for (challenge, addr) in challenges.iter().zip(outputs.iter()) {
                if let Some(claim) = output_claims.get(addr) {
                    let mut weighted = *claim;
                    weighted.mul_assign(challenge);
                    combined.add_assign(&weighted);
                }
            }
        }
        combined
    }

    fn from_gates(
        layer: &GKRLayerDescription,
        layer_idx: usize,
        batch_challenge_base: E,
        gkr_storage: &GKRStorage<F, E>,
        lookup_challenges_additive_part: E,
    ) -> Self {
        let mut collector = Self::new(batch_challenge_base);

        for gate in layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
        {
            match &gate.enforced_relation {
                NoFieldGKRRelation::Copy { input, output } => {
                    let is_base_field = gkr_storage.layers[layer_idx]
                        .base_field_inputs
                        .contains_key(input);

                    let kernel = if is_base_field {
                        KernelVariant::BaseCopy(BaseFieldCopyGKRRelation {
                            input: *input,
                            output: *output,
                        })
                    } else {
                        KernelVariant::ExtCopy(ExtensionCopyGKRRelation {
                            input: *input,
                            output: *output,
                        })
                    };
                    collector.register(kernel);
                }
                NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
                | NoFieldGKRRelation::TrivialProduct { input, output } => {
                    collector.register(KernelVariant::Product(SameSizeProductGKRRelation {
                        inputs: *input,
                        output: *output,
                    }));
                }
                NoFieldGKRRelation::MaskIntoIdentityProduct {
                    input,
                    mask,
                    output,
                } => {
                    collector.register(KernelVariant::MaskIdentity(
                        MaskIntoIdentityProductGKRRelation {
                            input: *input,
                            mask: *mask,
                            output: *output,
                        },
                    ));
                }
                NoFieldGKRRelation::LookupPair { input, output } => {
                    collector.register(KernelVariant::LookupPair(LookupPairGKRRelation {
                        inputs: *input,
                        outputs: *output,
                    }));
                }
                NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                    collector.register(KernelVariant::LookupBasePair(LookupBasePairGKRRelation {
                        inputs: *input,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    }));
                }
                NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                    input,
                    setup,
                    output,
                } => {
                    collector.register(KernelVariant::LookupBaseMinusMultiplicity(
                        LookupBaseMinusMultiplicityByBaseGKRRelation {
                            input: *input,
                            setup: *setup,
                            outputs: *output,
                            lookup_additive_challenge: lookup_challenges_additive_part,
                            _marker: core::marker::PhantomData,
                        },
                    ));
                }
                NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                    input,
                    remainder,
                    output,
                } => {
                    collector.register(KernelVariant::LookupUnbalanced(
                        LookupRationalPairWithUnbalancedBaseGKRRelation {
                            inputs: *input,
                            remainder: *remainder,
                            outputs: *output,
                            lookup_additive_challenge: lookup_challenges_additive_part,
                            _marker: core::marker::PhantomData,
                        },
                    ));
                }
                NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => todo!(),
                NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => todo!(),
                NoFieldGKRRelation::MaterializeSingleLookupInput { .. } => todo!(),
                NoFieldGKRRelation::MaterializedVectorLookupInput { .. } => todo!(),
                NoFieldGKRRelation::LookupWithCachedDensAndSetup { .. } => todo!(),
                NoFieldGKRRelation::LookupPairFromBaseInputs { .. } => todo!(),
                NoFieldGKRRelation::LookupUnbalancedPairWithBaseInputs { .. } => todo!(),
                NoFieldGKRRelation::LookupFromBaseInputsWithSetup { .. } => todo!(),
                NoFieldGKRRelation::LookupPairFromVectorInputs { .. } => todo!(),
            }
        }
        collector
    }

    fn evaluate_kernels_over_storage(
        &self,
        gkr_storage: &mut GKRStorage<F, E>,
        step: usize,
        folding_challenges: &[E],
        accumulator: &mut [[E; 2]],
        folding_steps: usize,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
        worker: &Worker,
    ) {
        for (kernel, batch_challenges) in self
            .kernels
            .iter()
            .zip(self.batch_challenges_per_kernel.iter())
        {
            kernel.evaluate_over_storage(
                gkr_storage,
                step,
                batch_challenges,
                folding_challenges,
                accumulator,
                folding_steps,
                last_evaluations,
                worker,
            );
        }
    }
}

fn run_sumcheck_loop<F: PrimeField, E: FieldExtension<F> + Field>(
    collector: &KernelCollector<F, E>,
    initial_claim: E,
    prev_challenges: &[E],
    eq_poly: &[Vec<E>],
    gkr_storage: &mut GKRStorage<F, E>,
    folding_steps: usize,
    worker: &Worker,
) -> (Vec<E>, BTreeMap<GKRAddress, [E; 2]>){
    let mut claim = initial_claim;
    let mut folding_challenges = Vec::with_capacity(folding_steps);
    let mut last_evaluations: BTreeMap<GKRAddress, [E; 2]> = BTreeMap::new();

    let mut eq_prefactor = E::ONE;

    let max_acc_size = 1 << (folding_steps - 1);
    let mut accumulator_buffer = vec![[E::ZERO; 2]; max_acc_size];

    for step in 0..folding_steps - 1 {
        let acc_size = 1 << (folding_steps - step - 1);
        let accumulator = &mut accumulator_buffer[..acc_size];
        accumulator.fill([E::ZERO; 2]);

        collector.evaluate_kernels_over_storage(
            gkr_storage,
            step,
            &folding_challenges,
            accumulator,
            folding_steps,
            &mut last_evaluations,
            worker,
        );

        // TODO: get from transcript
        let folding_challenge = E::from_base(F::from_u32_unchecked(42 + step as u32));

        let eq = &eq_poly[folding_steps - step - 1];
        debug_assert_eq!(eq.len(), acc_size);

        let [c0, c2] =
            evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(&accumulator, eq);

        let mut normalized_claim = claim;
        normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

        let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
            prev_challenges[step],
            normalized_claim,
            c0,
            c2,
        );

        // Verify: s(0) + s(1) == claim / eq_prefactor
        debug_assert!({
            let s0 = evaluate_small_univariate_poly::<F, E>(&coeffs, &E::ZERO);
            let s1 = evaluate_small_univariate_poly::<F, E>(&coeffs, &E::ONE);
            let mut sum = s0;
            sum.add_assign(&s1);
            sum.mul_assign(&eq_prefactor);
            sum == claim
        });

        // TODO: add coeffs to transcript
        claim = evaluate_small_univariate_poly::<F, E>(&coeffs, &folding_challenge);
        eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);

        folding_challenges.push(folding_challenge);
    }

    // Final step
    {
        let step = folding_steps - 1;
        let accumulator = &mut accumulator_buffer[..1];
        accumulator.fill([E::ZERO; 2]);

        collector.evaluate_kernels_over_storage(
            gkr_storage,
            step,
            &folding_challenges,
            accumulator,
            folding_steps,
            &mut last_evaluations,
            worker,
        );

        // TODO: get from transcript
        let folding_challenge = E::from_base(F::from_u32_unchecked(42 + step as u32));

        let [f0, f1] = accumulator[0];

        // eq_poly[1] = [1 - u_last, u_last]
        let [eq0, eq1]: [E; 2] = eq_poly[1].as_ref().try_into().unwrap();

        let mut t0 = eq0;
        t0.mul_assign(&f0);
        let mut t1 = eq1;
        t1.mul_assign(&f1);
        let mut claim_inner = t0;
        claim_inner.add_assign(&t1);

        let mut recomputed_claim = claim_inner;
        recomputed_claim.mul_assign(&eq_prefactor);

        debug_assert_eq!(claim, recomputed_claim, "Final claim verification failed");

        folding_challenges.push(folding_challenge);
    }

    (
        folding_challenges,
        last_evaluations,
    )
}

pub fn evaluate_sumcheck_for_layer<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    _compiled_circuit: &cs::gkr_compiler::GKRCircuitArtifact<F>,
    _external_challenges: &crate::gkr::prover::GKRExternalChallenges<F, E>,
    trace_len: usize,
    lookup_challenges_additive_part: E,
    _constraints_batch_challenge: E,
    worker: &Worker,
) {
    println!("Evaluating layer {} in sumcheck direction", layer_idx);

    let output_layer_idx = layer_idx + 1;

    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    let prev_challenges = claim_points
        .get(&output_layer_idx)
        .expect("claim points for output layer must exist");

    debug_assert!(trace_len.is_power_of_two());
    let folding_steps = trace_len.trailing_zeros() as usize;
    assert!(folding_steps > 1, "need at least 2 folding steps");

    // Precompute eq polynomial evaluations over the boolean hypercube
    let eq_poly = make_eq_poly_in_full::<F, E>(prev_challenges);

    // TODO: get from transcript
    let batch_challenge_base = E::from_base(F::from_u32_unchecked(0xff));

    let collector = KernelCollector::from_gates(
        layer,
        layer_idx,
        batch_challenge_base,
        gkr_storage,
        lookup_challenges_additive_part,
    );
    debug_assert!(!collector.is_empty());

    let claim = collector.compute_combined_claim(output_claims);

    let (folding_challenges, last_evaluations) = run_sumcheck_loop(
        &collector,
        claim,
        prev_challenges,
        &eq_poly,
        gkr_storage,
        folding_steps,
        worker,
    );

    // After sumcheck completes, extract claims for the input layer
    let last_r = folding_challenges
        .last()
        .expect("must have at least one folding challenge");

    let new_claims: BTreeMap<_, _> = last_evaluations
        .iter()
        .map(|(addr, &[f0, f1])| (*addr, interpolate_linear::<F, E>(f0, f1, last_r)))
        .collect();

    claims_storage.insert(layer_idx, new_claims);
    claim_points.insert(layer_idx, folding_challenges);
}

#[inline]
fn interpolate_linear<F: PrimeField, E: FieldExtension<F> + Field>(f0: E, f1: E, r: &E) -> E {
    let mut result = f1;
    result.sub_assign(&f0);
    result.mul_assign(r);
    result.add_assign(&f0);
    result
}
