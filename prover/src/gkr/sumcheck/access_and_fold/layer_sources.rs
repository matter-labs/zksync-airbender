use super::*;

impl<F: PrimeField, E: FieldExtension<F> + Field> GKRStorage<F, E> {
    pub fn get_base_field_initial_source(&self, input: &GKRAddress) -> BaseFieldPolySource<F> {
        let layer = match *input {
            GKRAddress::ScratchSpace(..) => {
                unreachable!()
            }
            GKRAddress::Cached { layer, .. } => layer,
            GKRAddress::InnerLayer { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => 0,
        };
        let Some(source) = self.layers[layer].base_field_inputs.get(input) else {
            panic!("Polynomial with address {:?} is missing from input sources for base field polys for evaluating caller {:?}", input, core::panic::Location::caller());
        };
        source.accessor()
    }

    pub fn get_extension_field_initial_source(
        &self,
        input: &GKRAddress,
    ) -> ExtensionFieldPolyInitialSource<F, E> {
        let layer = match *input {
            GKRAddress::ScratchSpace(..) => {
                unreachable!()
            }
            GKRAddress::Cached { layer, .. } => layer,
            GKRAddress::InnerLayer { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => 0,
        };
        let Some(source) = self.layers[layer].extension_field_inputs.get(input) else {
            panic!("Polynomial with address {:?} is missing from input sources for extension field polys for evaluating caller {:?}", input, core::panic::Location::caller());
        };
        source.accessor()
    }
}
