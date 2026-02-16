use std::collections::BTreeMap;

use field::{PrimeField, FieldExtension, Field};
use crate::gkr::sumcheck::access_and_fold::GKRStorage;
use crate::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchConstraintEvalGKRRelation, BatchedGKRKernel,
    ExtensionCopyGKRRelation, LookupBaseExtMinusBaseExtGKRRelation,
    LookupBaseMinusMultiplicityByBaseGKRRelation, LookupBasePairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
use crate::worker::Worker;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRLayerDescription, NoFieldGKRRelation};

#[derive(Debug)]
pub(super) enum KernelVariant<F: PrimeField, E: FieldExtension<F> + Field> {
    // (kernel, challenge, output)
    BaseCopy(BaseFieldCopyGKRRelation, [E; 1], GKRAddress),
    ExtCopy(ExtensionCopyGKRRelation, [E; 1], GKRAddress),
    Product(SameSizeProductGKRRelation, [E; 1], GKRAddress),
    MaskIdentity(MaskIntoIdentityProductGKRRelation, [E; 1], GKRAddress),
    LookupPair(LookupPairGKRRelation, [E; 2], [GKRAddress; 2]),
    LookupBasePair(LookupBasePairGKRRelation<F, E>, [E; 2], [GKRAddress; 2]),
    LookupBaseMinusMultiplicity(LookupBaseMinusMultiplicityByBaseGKRRelation<F, E>, [E; 2], [GKRAddress; 2]),
    LookupUnbalanced(LookupRationalPairWithUnbalancedBaseGKRRelation<F, E>, [E; 2], [GKRAddress; 2]),
    LookupWithCachedDensAndSetup(LookupBaseExtMinusBaseExtGKRRelation, [E; 2], [GKRAddress; 2]),
    EnforceConstraintsMaxQuadratic(BatchConstraintEvalGKRRelation<F, E>, [E; 1]),
}

macro_rules! dispatch_kernel {
    ($self:expr, |$k:ident| $body:expr) => {
        match $self {
            KernelVariant::BaseCopy(ref $k, _, _) => $body,
            KernelVariant::ExtCopy(ref $k, _, _) => $body,
            KernelVariant::Product(ref $k, _, _) => $body,
            KernelVariant::MaskIdentity(ref $k, _, _) => $body,
            KernelVariant::LookupPair(ref $k, _, _) => $body,
            KernelVariant::LookupBasePair(ref $k, _, _) => $body,
            KernelVariant::LookupBaseMinusMultiplicity(ref $k, _, _) => $body,
            KernelVariant::LookupUnbalanced(ref $k, _, _) => $body,
            KernelVariant::LookupWithCachedDensAndSetup(ref $k, _, _) => $body,
            KernelVariant::EnforceConstraintsMaxQuadratic(ref $k, _) => $body,
        }
    };
}

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelVariant<F, E> {
    pub fn num_challenges(&self) -> usize {
        dispatch_kernel!(self, |k| BatchedGKRKernel::<F, E>::num_challenges(k))
    }

    pub fn batch_challenges(&self) -> &[E] {
        match self {
            KernelVariant::BaseCopy(_, bc,_) => bc,
            KernelVariant::ExtCopy(_, bc, _) => bc,
            KernelVariant::Product(_, bc, _) => bc,
            KernelVariant::MaskIdentity(_, bc, _) => bc,
            KernelVariant::LookupPair(_, bc, _) => bc,
            KernelVariant::LookupBasePair(_, bc, _) => bc,
            KernelVariant::LookupBaseMinusMultiplicity(_, bc, _) => bc,
            KernelVariant::LookupUnbalanced(_, bc, _) => bc,
            KernelVariant::LookupWithCachedDensAndSetup(_, bc, _) => bc,
            KernelVariant::EnforceConstraintsMaxQuadratic(_, bc) => bc,
        }
    }

    pub fn evaluate_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        step: usize,
        folding_challenges: &[E],
        accumulator: &mut [[E; 2]],
        total_sumcheck_rounds: usize,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
        worker: &Worker,
    ) {
        let batch_challenges = self.batch_challenges();

        debug_assert_eq!(batch_challenges.len(), self.num_challenges());

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

    pub fn from_enforced_relations(
        relation: &NoFieldGKRRelation,
        layer_idx: usize,
        gkr_storage: &GKRStorage<F, E>,
        lookup_challenges_additive_part: E,
        challenge_for_constraints: E,
        num_base_layer_memory_polys: usize,
        num_base_layer_witness_polys: usize,
        current_batch_challenge: &mut E,
        batch_challenge_base: &E,
    ) -> Self {
        let mut get_challenge = || {
            let c = *current_batch_challenge;
            current_batch_challenge.mul_assign(batch_challenge_base);
            c
        };

        match relation {
            NoFieldGKRRelation::Copy { input, output } => {
                let challenge = [get_challenge()];
                let is_base_field = gkr_storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(input);
                if is_base_field {
                    KernelVariant::BaseCopy(
                        BaseFieldCopyGKRRelation { input: *input, output: *output },
                        challenge,
                        *output,
                    )
                } else {
                    KernelVariant::ExtCopy(
                        ExtensionCopyGKRRelation { input: *input, output: *output },
                        challenge,
                        *output,
                    )
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let challenge = [get_challenge()];
                KernelVariant::Product(
                    SameSizeProductGKRRelation { inputs: *input, output: *output },
                    challenge,
                    *output,
                )
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct { input, mask, output } => {
                let challenge = [get_challenge()];
                KernelVariant::MaskIdentity(
                    MaskIntoIdentityProductGKRRelation { input: *input, mask: *mask, output: *output },
                    challenge,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupPair { input, output } => {
                let challenges = [get_challenge(), get_challenge()];
                KernelVariant::LookupPair(
                    LookupPairGKRRelation { inputs: *input, outputs: *output },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let challenges = [get_challenge(), get_challenge()];
                KernelVariant::LookupBasePair(
                    LookupBasePairGKRRelation {
                        inputs: *input,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup { input, setup, output } => {
                let challenges = [get_challenge(), get_challenge()];
                KernelVariant::LookupBaseMinusMultiplicity(
                    LookupBaseMinusMultiplicityByBaseGKRRelation {
                        input: *input,
                        setup: *setup,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs { input, remainder, output } => {
                let challenges = [get_challenge(), get_challenge()];
                KernelVariant::LookupUnbalanced(
                    LookupRationalPairWithUnbalancedBaseGKRRelation {
                        inputs: *input,
                        remainder: *remainder,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup { input, setup, output } => {
                let challenges = [get_challenge(), get_challenge()];
                KernelVariant::LookupWithCachedDensAndSetup(
                    LookupBaseExtMinusBaseExtGKRRelation {
                        nums: [input[0], setup[0]],
                        dens: [input[1], setup[1]],
                        outputs: *output,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let challenge = [get_challenge()];
                KernelVariant::EnforceConstraintsMaxQuadratic(
                    BatchConstraintEvalGKRRelation::new(
                        input,
                        num_base_layer_memory_polys,
                        num_base_layer_witness_polys,
                        challenge_for_constraints,
                    ),
                    challenge,
                )
            }
            NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => todo!(),
            NoFieldGKRRelation::MaterializeSingleLookupInput { .. } => todo!(),
            NoFieldGKRRelation::MaterializedVectorLookupInput { .. } => todo!(),
            NoFieldGKRRelation::LookupPairFromBaseInputs { .. } => todo!(),
            NoFieldGKRRelation::LookupUnbalancedPairWithBaseInputs { .. } => todo!(),
            NoFieldGKRRelation::LookupFromBaseInputsWithSetup { .. } => todo!(),
            NoFieldGKRRelation::LookupPairFromVectorInputs { .. } => todo!(),
        }
    }

    pub fn compute_output_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        match self {
            KernelVariant::BaseCopy(_, challenge, output_addr)
            | KernelVariant::ExtCopy(_, challenge, output_addr)
            | KernelVariant::Product(_, challenge, output_addr)
            | KernelVariant::MaskIdentity(_, challenge, output_addr) => {
                let mut res = challenge[0];
                res.mul_assign(output_claims.get(output_addr).expect("output claim must exist"));
                res
            }
            KernelVariant::LookupPair(_, challenges, addrs)
            | KernelVariant::LookupBasePair(_, challenges, addrs)
            | KernelVariant::LookupBaseMinusMultiplicity(_, challenges, addrs)
            | KernelVariant::LookupUnbalanced(_, challenges, addrs)
            | KernelVariant::LookupWithCachedDensAndSetup(_, challenges, addrs) => {
                let mut res = E::ZERO;
                for (challenge, addr) in challenges.iter().zip(addrs.iter()) {
                    if let Some(claim) = output_claims.get(addr) {
                        let mut weighted = *claim;
                        weighted.mul_assign(challenge);
                        res.add_assign(&weighted);
                    }
                }
                res
            }
            // No output
            KernelVariant::EnforceConstraintsMaxQuadratic(..) => E::ZERO,
        }
    }
}

pub(super) struct KernelCollector<F: PrimeField, E: FieldExtension<F> + Field> {
    kernels: Vec<KernelVariant<F, E>>,
    current_batch_challenge: E,
    batch_challenge_base: E,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    pub(super) fn new(batch_challenge_base: E) -> Self {
        Self {
            kernels: Vec::new(),
            current_batch_challenge: E::ONE,
            batch_challenge_base,
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.kernels.is_empty()
    }

    pub(super) fn register(&mut self, kernel: KernelVariant<F, E>) {
        // TODO: these kernels have a bug in them
        match kernel {
            KernelVariant::EnforceConstraintsMaxQuadratic(..) => {},
                | KernelVariant::LookupBaseMinusMultiplicity(..) => {},
            _ => self.kernels.push(kernel),
        }
    }

    pub(super) fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        self
            .kernels
            .iter()
            .fold(E::ZERO, |mut acc, kernel| {
                acc.add_assign(&kernel.compute_output_claim(output_claims));
                acc
            })
    }

    pub(super) fn from_layer(
        layer: &GKRLayerDescription,
        layer_idx: usize,
        batch_challenge_base: E,
        gkr_storage: &GKRStorage<F, E>,
        lookup_challenges_additive_part: E,
        challenge_for_constraints: E,
        num_base_layer_memory_polys: usize,
        num_base_layer_witness_polys: usize,
    ) -> Self {
        let mut collector = Self::new(batch_challenge_base);

        debug_assert!(layer.gates.is_empty() ^ layer.gates_with_external_connections.is_empty());

        let batch_base = collector.batch_challenge_base;

        for gate in layer.gates.iter().chain(layer.gates_with_external_connections.iter()) {
            let kernel = KernelVariant::from_enforced_relations(
                &gate.enforced_relation,
                layer_idx,
                gkr_storage,
                lookup_challenges_additive_part,
                challenge_for_constraints,
                num_base_layer_memory_polys,
                num_base_layer_witness_polys,
                &mut collector.current_batch_challenge,
                &batch_base,
            );
            collector.register(kernel);
        }

        collector
    }

    pub(super) fn evaluate_kernels_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        step: usize,
        folding_challenges: &[E],
        accumulator: &mut [[E; 2]],
        folding_steps: usize,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
        worker: &Worker,
    ) {
        self
            .kernels
            .iter()
            .for_each(|kernel| kernel.evaluate_over_storage(storage, step, folding_challenges, accumulator, folding_steps, last_evaluations, worker));
    }
}