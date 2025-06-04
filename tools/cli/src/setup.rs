use prover::{
    fft::GoodAllocator,
    field::Mersenne31Field,
    risc_v_simulator::cycle::{IMStandardIsaConfig, IWithoutByteAccessIsaConfigWithDelegation},
};
use prover_examples::create_circuit_setup;
use setups::{DelegationCircuitPrecomputations, MainCircuitPrecomputations};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::{collections::hash_map::DefaultHasher, sync::Arc};

#[derive(Default)]
pub struct SetupCache<A: GoodAllocator, B: GoodAllocator> {
    pub main_circuit_setup: HashMap<
        u64,
        (
            Arc<MainCircuitPrecomputations<IMStandardIsaConfig, A, B>>,
            Arc<Vec<Mersenne31Field, B>>,
        ),
    >,
    pub reduced_circuit_setup: HashMap<
        u64,
        (
            Arc<MainCircuitPrecomputations<IWithoutByteAccessIsaConfigWithDelegation, A, B>>,
            Arc<Vec<Mersenne31Field, B>>,
        ),
    >,
    pub delegations: Arc<Vec<(u32, DelegationCircuitPrecomputations<A, B>)>>,
    pub delegation_evals: Arc<Vec<(u32, Arc<Vec<Mersenne31Field, B>>)>>,
}

impl<A: GoodAllocator, B: GoodAllocator> SetupCache<A, B> {
    pub fn get_or_create_main_circuit(
        &mut self,
        bytecode: &Vec<u32>,
    ) -> &(
        Arc<MainCircuitPrecomputations<IMStandardIsaConfig, A, B>>,
        Arc<Vec<Mersenne31Field, B>>,
    ) {
        let mut hasher = DefaultHasher::new();
        bytecode.hash(&mut hasher);
        let hash = hasher.finish();

        self.main_circuit_setup.entry(hash).or_insert_with(|| {
            let worker = worker::Worker::new_with_num_threads(8);
            let setup = setups::get_main_riscv_circuit_setup(&bytecode, &worker);
            let eval = create_circuit_setup(&setup.setup.ldes[0].trace);
            (Arc::new(setup), Arc::new(eval))
        })
    }
    pub fn get_or_create_reduced_circuit(
        &mut self,
        bytecode: &Vec<u32>,
    ) -> &(
        Arc<MainCircuitPrecomputations<IWithoutByteAccessIsaConfigWithDelegation, A, B>>,
        Arc<Vec<Mersenne31Field, B>>,
    ) {
        let mut hasher = DefaultHasher::new();
        bytecode.hash(&mut hasher);
        let hash = hasher.finish();

        self.reduced_circuit_setup.entry(hash).or_insert_with(|| {
            let worker = worker::Worker::new_with_num_threads(8);
            // Compute the setup here
            let setup = setups::get_reduced_riscv_circuit_setup(&bytecode, &worker);
            let eval = create_circuit_setup(&setup.setup.ldes[0].trace);
            (Arc::new(setup), Arc::new(eval))
        })
    }

    pub fn get_or_create_delegations(
        &mut self,
    ) -> (
        Arc<Vec<(u32, DelegationCircuitPrecomputations<A, B>)>>,
        Arc<Vec<(u32, Arc<Vec<Mersenne31Field, B>>)>>,
    ) {
        if self.delegations.is_empty() {
            let worker = worker::Worker::new_with_num_threads(8);
            // Compute the setup here
            self.delegations = Arc::new(setups::all_delegation_circuits_precomputations(&worker));
            let mut delegation_evals = Vec::new();
            for (circuit, setup) in self.delegations.iter() {
                let eval = create_circuit_setup(&setup.setup.ldes[0].trace);
                delegation_evals.push((circuit.clone(), Arc::new(eval)));
            }
            self.delegation_evals = Arc::new(delegation_evals);
        }
        (self.delegations.clone(), self.delegation_evals.clone())
    }
}
