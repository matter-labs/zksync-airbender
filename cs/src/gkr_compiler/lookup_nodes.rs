use super::*;
use crate::definitions::gkr::NoFieldSingleColumnLookupRelation;
use crate::definitions::{Degree1Constraint, GKRAddress};
use crate::gkr_compiler::graph::GraphHolder;

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum LookupNumerator {
    Identity,
    PositiveMultiplicity(GKRAddress),
    NegativeMultiplicity(GKRAddress),
    ExtensionValueWithAllConstantsMixed(GKRAddress),
    // LinearNumeratorFromInitialAccumulationCaches([GKRAddress; 2]),
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum LookupDenominator {
    // single address, that contains base field values. Gate should mix lookup's additive constant
    BaseFieldValueWithoutAdditiveConstant(GKRAddress),
    // single address, that contains extension field values (for vectorized lookup). Gate should mix lookup's additive constant
    ExtensionFieldValueWithoutAdditiveConstant(GKRAddress),
    // extension field element - either we added an additive constant before, or it it came from previous
    // logUp reduction
    ExtensionValueWithAllConstantsMixed(GKRAddress),
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LookupInputRelation<F: PrimeField> {
    pub inputs: Vec<Degree1Constraint<F>>,
    pub table_id: Option<Degree1Constraint<F>>,
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MaterializeSingleInputNode {
    pub(crate) input: NoFieldSingleColumnLookupRelation,
    pub(crate) range_check_width: u32,
}

impl GKRGate for MaterializeSingleInputNode {
    type Output = GKRAddress;

    fn short_name(&self) -> String {
        "Materialize single lookup input node".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = graph.add_intermediate_variable_at_layer(output_layer);

        if self.input.input.is_trivial_single_input() {
            // just copy
            let input = self.input.input.linear_terms[0].1;
            let relation = NoFieldGKRRelation::Copy { input, output };
            graph.add_enforced_relation(relation.clone(), output_layer);

            (output, relation)
        } else {
            let cached_input = NoFieldGKRCacheRelation::SingleColumnLookup {
                relation: self.input.clone(),
                range_check_width: self.range_check_width as usize,
            };
            assert!(output_layer > 0);
            let layer_for_caches = output_layer - 1;
            let cached_input = graph.add_cached_relation(cached_input, layer_for_caches);

            let relation = NoFieldGKRRelation::Copy {
                input: cached_input,
                output,
            };
            graph.add_enforced_relation(relation.clone(), output_layer);

            (output, relation)
        }
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MaterializeVectorInputNode(pub(crate) NoFieldVectorLookupRelation);

impl GKRGate for MaterializeVectorInputNode {
    type Output = GKRAddress;

    fn short_name(&self) -> String {
        "Materialize vector lookup input node".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = graph.add_intermediate_variable_at_layer(output_layer);
        // TODO: decide to cache or not, maybe adaptively based on the number of terms

        let relation = NoFieldGKRRelation::MaterializedVectorLookupInput {
            input: self.0.clone(),
            output,
        };
        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LookupMaskedWitnessMinusSetupInputNode {
    pub mask: GKRAddress,
    pub input: NoFieldVectorLookupRelation,
    pub multiplicity: GKRAddress,
    pub setup: Box<[GKRAddress]>,
}

impl GKRGate for LookupMaskedWitnessMinusSetupInputNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "Mask/vector_input - multiplicity/vector_setup".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = [(); 2].map(|_| graph.add_intermediate_variable_at_layer(output_layer));
        let cached_input = NoFieldGKRCacheRelation::VectorizedLookup(self.input.clone());
        let cached_setup = NoFieldGKRCacheRelation::VectorizedLookupSetup(self.setup.clone());
        assert!(output_layer > 0);
        let layer_for_caches = output_layer - 1;
        let cached_input = graph.add_cached_relation(cached_input, layer_for_caches);
        let cached_setup = graph.add_cached_relation(cached_setup, layer_for_caches);

        let relation = NoFieldGKRRelation::LookupWithCachedDensAndSetup {
            input: [self.mask, cached_input],
            setup: [self.multiplicity, cached_setup],
            output,
        };
        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LookupSingleColumnWitnessMinusSetupInputNode {
    pub input: NoFieldSingleColumnLookupRelation,
    pub multiplicity: GKRAddress,
    pub setup: GKRAddress,
    pub range_check_width: u32,
}

impl GKRGate for LookupSingleColumnWitnessMinusSetupInputNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "1/single_input - multiplicity/single_setup".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = [(); 2].map(|_| graph.add_intermediate_variable_at_layer(output_layer));

        // We will be lazy - will cache the input

        let input = if self.input.input.is_trivial_single_input() {
            self.input.input.linear_terms[0].1
        } else {
            let cached_input = NoFieldGKRCacheRelation::SingleColumnLookup {
                relation: self.input.clone(),
                range_check_width: self.range_check_width as usize,
            };
            assert!(output_layer > 0);
            let layer_for_caches = output_layer - 1;
            let cached_input = graph.add_cached_relation(cached_input, layer_for_caches);

            cached_input
        };

        let relation = NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
            input,
            setup: [self.multiplicity, self.setup],
            output,
        };

        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LookupSingleColumnWitnessPairAggregationNode {
    pub lhs: NoFieldSingleColumnLookupRelation,
    pub rhs: NoFieldSingleColumnLookupRelation,
    pub range_check_width: u32,
}

impl GKRGate for LookupSingleColumnWitnessPairAggregationNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "1/single_input + 1/single_input".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = [(); 2].map(|_| graph.add_intermediate_variable_at_layer(output_layer));

        let input = [&self.lhs, &self.rhs].map(|input| {
            if input.input.is_trivial_single_input() {
                input.input.linear_terms[0].1
            } else {
                let cached_input = NoFieldGKRCacheRelation::SingleColumnLookup {
                    relation: input.clone(),
                    range_check_width: self.range_check_width as usize,
                };
                assert!(output_layer > 0);
                let layer_for_caches = output_layer - 1;
                let cached_input = graph.add_cached_relation(cached_input, layer_for_caches);

                cached_input
            }
        });

        let relation = NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output };

        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LookupExplicitPairAggregationNode {
    pub lhs_num: GKRAddress,
    pub lhs_den: GKRAddress,
    pub rhs_num: GKRAddress,
    pub rhs_den: GKRAddress,
}

impl GKRGate for LookupExplicitPairAggregationNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "a/b + c/d".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = [(); 2].map(|_| graph.add_intermediate_variable_at_layer(output_layer));

        let relation = NoFieldGKRRelation::AggregateLookupRationalPair {
            input: [[self.lhs_num, self.lhs_den], [self.rhs_num, self.rhs_den]],
            output,
        };
        for el in [self.lhs_num, self.lhs_den, self.rhs_num, self.rhs_den] {
            el.assert_as_dependency_for_layer(output_layer);
        }
        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LookupExplicitPairWithSingleColumnInputAggregationNode {
    pub lhs_num: GKRAddress,
    pub lhs_den: GKRAddress,
    pub base_input: NoFieldSingleColumnLookupRelation,
    pub range_check_width: u32,
}

impl GKRGate for LookupExplicitPairWithSingleColumnInputAggregationNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "a/b + 1/single_input".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        // cache the explicit value
        let base_input = if self.base_input.input.is_trivial_single_input() {
            self.base_input.input.linear_terms[0].1
        } else {
            let cached_input = NoFieldGKRCacheRelation::SingleColumnLookup {
                relation: self.base_input.clone(),
                range_check_width: self.range_check_width as usize,
            };
            assert!(output_layer > 0);
            let layer_for_caches = output_layer - 1;
            let cached_input = graph.add_cached_relation(cached_input, layer_for_caches);

            cached_input
        };

        let node = LookupExplicitPairWithSingleColumnMaterializedInputAggregationNode {
            lhs_num: self.lhs_num,
            lhs_den: self.lhs_den,
            base_input,
            range_check_width: self.range_check_width,
        };
        node.add_at_layer(graph, output_layer)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LookupExplicitPairWithSingleColumnMaterializedInputAggregationNode {
    pub lhs_num: GKRAddress,
    pub lhs_den: GKRAddress,
    pub base_input: GKRAddress,
    pub range_check_width: u32,
}

impl GKRGate for LookupExplicitPairWithSingleColumnMaterializedInputAggregationNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "a/b + 1/single_input".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = [(); 2].map(|_| graph.add_intermediate_variable_at_layer(output_layer));

        let relation = NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
            input: [self.lhs_num, self.lhs_den],
            remainder: self.base_input,
            output,
        };

        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct VectorLookupWitnessPairAggregationFromCachesNode {
    pub lhs: NoFieldVectorLookupRelation,
    pub rhs: NoFieldVectorLookupRelation,
}

impl GKRGate for VectorLookupWitnessPairAggregationFromCachesNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "1/vector_input + 1/vector_input".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = [(); 2].map(|_| graph.add_intermediate_variable_at_layer(output_layer));

        let input = [&self.lhs, &self.rhs].map(|input| {
            // cache
            let cached_input = NoFieldGKRCacheRelation::VectorizedLookup(input.clone());
            assert!(output_layer > 0);
            let layer_for_caches = output_layer - 1;
            let cached_input = graph.add_cached_relation(cached_input, layer_for_caches);

            cached_input
        });

        let relation = NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output };

        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct VectorLookupExplicitPairWithInputAggregationNode {
    pub lhs_num: GKRAddress,
    pub lhs_den: GKRAddress,
    pub vector_input: NoFieldVectorLookupRelation,
}

impl GKRGate for VectorLookupExplicitPairWithInputAggregationNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "a/b + 1/vector_input".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        // cache the explicit value
        let cached_input = NoFieldGKRCacheRelation::VectorizedLookup(self.vector_input.clone());
        assert!(output_layer > 0);
        let layer_for_caches = output_layer - 1;
        let cached_input = graph.add_cached_relation(cached_input, layer_for_caches);

        let node = VectorLookupExplicitPairWithMaterializedInputAggregationNode {
            lhs_num: self.lhs_num,
            lhs_den: self.lhs_den,
            vector_input: cached_input,
        };
        node.add_at_layer(graph, output_layer)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct VectorLookupExplicitPairWithMaterializedInputAggregationNode {
    pub lhs_num: GKRAddress,
    pub lhs_den: GKRAddress,
    pub vector_input: GKRAddress,
}

impl GKRGate for VectorLookupExplicitPairWithMaterializedInputAggregationNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "a/b + 1/vector_input".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = [(); 2].map(|_| graph.add_intermediate_variable_at_layer(output_layer));

        let relation = NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
            input: [self.lhs_num, self.lhs_den],
            remainder: self.vector_input,
            output,
        };

        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct VectorLookupWitnessMinusSetupInputNode {
    pub input: NoFieldVectorLookupRelation,
    pub multiplicity: GKRAddress,
    pub setup: Box<[GKRAddress]>,
}

impl GKRGate for VectorLookupWitnessMinusSetupInputNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "1/vector_input - multiplicity/vector_setup".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        // We will be lazy - will cache the input

        let cached_input = NoFieldGKRCacheRelation::VectorizedLookup(self.input.clone());
        assert!(output_layer > 0);
        let layer_for_caches = output_layer - 1;
        let cached_input = graph.add_cached_relation(cached_input, layer_for_caches);

        let node = VectorLookupMaterializedWitnessMinusSetupInputNode {
            input: cached_input,
            multiplicity: self.multiplicity,
            setup: self.setup.clone(),
        };
        node.add_at_layer(graph, output_layer)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct VectorLookupMaterializedWitnessMinusSetupInputNode {
    pub input: GKRAddress,
    pub multiplicity: GKRAddress,
    pub setup: Box<[GKRAddress]>,
}

impl GKRGate for VectorLookupMaterializedWitnessMinusSetupInputNode {
    type Output = [GKRAddress; 2];

    fn short_name(&self) -> String {
        "1/vector_input - multiplicity/vector_setup".to_string()
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = [(); 2].map(|_| graph.add_intermediate_variable_at_layer(output_layer));

        let cached_setup = NoFieldGKRCacheRelation::VectorizedLookupSetup(self.setup.clone());
        assert!(output_layer > 0);
        let layer_for_caches = output_layer - 1;
        let cached_setup = graph.add_cached_relation(cached_setup, layer_for_caches);

        let relation = NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
            input: self.input,
            setup: [self.multiplicity, cached_setup],
            output,
        };

        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}
