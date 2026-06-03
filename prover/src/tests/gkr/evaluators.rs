use super::*;

pub mod add_sub_lui_auipc_mop {
    use crate::gkr::sumcheck::SumcheckEvaluator;
    use ::field::*;
    use cs::definitions::gkr::GKRExternalChallengesProvider;
    use cs::definitions::*;
    use sumcheck_common::representation::*;

    // include!("../../../generated_evaluators/add_sub_lui_auipc_mop_generated_gkr.rs");
    include!("../../../../sumcheck_common/generated.rs");

    pub struct AddSubLuiAuipcMopEvaluator;

    impl<F: PrimeField, E: FieldExtension<F> + Field> SumcheckEvaluator<F, E>
        for AddSubLuiAuipcMopEvaluator
    {
        fn get_layer_evaluator_for_initial_round<
            S: sumcheck_common::representation::SumcheckRoundSource<F, E>,
            C: cs::definitions::gkr::GKRExternalChallengesProvider<F, E>,
        >(
            layer_idx: usize,
        ) -> fn(
            &[S::BaseInputAccessor],
            &[S::ExtInputAccessor],
            &[S::BaseInputAccessor],
            &[S::ExtInputAccessor],
            &[E], // batching
            &C,
            &[E], // lookup linearization
            &E,   // lookup additive
            &<S::BaseFieldInput as sumcheck_common::representation::EvaluationRepresentaionBase<
                F,
                E,
            >>::CTX,
            &<S::ExtFieldInput as sumcheck_common::representation::EvaluationRepresentaionBase<
                F,
                E,
            >>::CTX,
            &[E], // eq poly
            core::ops::Range<usize>,
        ) -> [E; 2] {
            match layer_idx {
                0 => layer_0_initial_round::<F, E, S, C> as _,
                _ => {
                    todo!()
                }
            }
        }

        fn get_layer_evaluator<
            S: sumcheck_common::representation::SumcheckRoundSource<F, E>,
            C: cs::definitions::gkr::GKRExternalChallengesProvider<F, E>,
            const EXPLICIT_FORM: bool,
        >(
            layer_idx: usize,
        ) -> fn(
            &[S::BaseInputAccessor],
            &[S::ExtInputAccessor],
            &[E],
            &C,
            &[E],
            &E,
            &<S::BaseFieldInput as sumcheck_common::representation::EvaluationRepresentaionBase<
                F,
                E,
            >>::CTX,
            &<S::ExtFieldInput as sumcheck_common::representation::EvaluationRepresentaionBase<
                F,
                E,
            >>::CTX,
            &[E],
            core::ops::Range<usize>,
        ) -> [E; 2] {
            match layer_idx {
                0 => layer_0::<F, E, S, C, EXPLICIT_FORM> as _,
                _ => {
                    todo!()
                }
            }
        }
    }
}
