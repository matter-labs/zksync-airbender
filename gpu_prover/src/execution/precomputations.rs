use cs::one_row_compiler::CompiledCircuitArtifact;
use fft::{GoodAllocator, LdePrecomputations, Twiddles};
use field::{Mersenne31Complex, Mersenne31Field};
use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength, MerkleTreeConstructor};
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::trace_holder::RowMajorTrace;
use std::alloc::Global;
use std::sync::Arc;
use trace_and_split::setups::{DelegationCircuitPrecomputations, MainCircuitPrecomputations};

type BF = Mersenne31Field;

#[derive(Clone)]
pub struct CircuitPrecomputationsHost<A: GoodAllocator, B: GoodAllocator = Global> {
    pub compiled_circuit: Arc<CompiledCircuitArtifact<BF>>,
    pub twiddles: Arc<Twiddles<Mersenne31Complex, B>>,
    pub lde_precomputations: Arc<LdePrecomputations<B>>,
    pub setup: Arc<Vec<BF, A>>,
    pub tree_caps: Vec<MerkleTreeCapVarLength>,
}

fn get_setup_from_row_major_trace<const N: usize, A: GoodAllocator, B: GoodAllocator>(
    trace: &RowMajorTrace<BF, N, B>,
) -> Arc<Vec<BF, A>> {
    let mut setup_evaluations = Vec::with_capacity_in(trace.as_slice().len(), A::default());
    unsafe { setup_evaluations.set_len(trace.as_slice().len()) };
    transpose::transpose(
        trace.as_slice(),
        &mut setup_evaluations,
        trace.padded_width,
        trace.len(),
    );
    setup_evaluations.truncate(trace.len() * trace.width());
    Arc::new(setup_evaluations)
}

impl<C: MachineConfig, A: GoodAllocator, B: GoodAllocator> From<MainCircuitPrecomputations<C, B, A>>
    for CircuitPrecomputationsHost<A, B>
{
    fn from(precomputations: MainCircuitPrecomputations<C, B, A>) -> Self {
        let MainCircuitPrecomputations {
            compiled_circuit,
            twiddles,
            lde_precomputations,
            setup,
            ..
        } = precomputations;
        let tree_caps = DefaultTreeConstructor::dump_caps(&setup.trees);
        CircuitPrecomputationsHost {
            compiled_circuit: Arc::new(compiled_circuit),
            twiddles: Arc::new(twiddles),
            lde_precomputations: Arc::new(lde_precomputations),
            setup: get_setup_from_row_major_trace(&setup.ldes[0].trace),
            tree_caps,
        }
    }
}

impl<A: GoodAllocator, B: GoodAllocator> From<DelegationCircuitPrecomputations<B, A>>
    for CircuitPrecomputationsHost<A, B>
{
    fn from(precomputations: DelegationCircuitPrecomputations<B, A>) -> Self {
        let DelegationCircuitPrecomputations {
            compiled_circuit,
            twiddles,
            lde_precomputations,
            setup,
            ..
        } = precomputations;
        let tree_caps = DefaultTreeConstructor::dump_caps(&setup.trees);
        CircuitPrecomputationsHost {
            compiled_circuit: Arc::new(compiled_circuit.compiled_circuit),
            twiddles: Arc::new(twiddles),
            lde_precomputations: Arc::new(lde_precomputations),
            setup: get_setup_from_row_major_trace(&setup.ldes[0].trace),
            tree_caps,
        }
    }
}
