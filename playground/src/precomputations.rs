use cs::one_row_compiler::CompiledCircuitArtifact;
use fft::{GoodAllocator, LdePrecomputations, Twiddles};
use field::{Mersenne31Complex, Mersenne31Field};
use risc_v_simulator::cycle::MachineConfig;
use std::sync::Arc;
use trace_and_split::setups::{DelegationCircuitPrecomputations, MainCircuitPrecomputations};
use trace_holder::RowMajorTrace;

type BF = Mersenne31Field;

#[derive(Clone)]
pub struct CircuitPrecomputationsHost<A: GoodAllocator, B: GoodAllocator> {
    pub compiled_circuit: Arc<CompiledCircuitArtifact<BF>>,
    pub twiddles: Arc<Twiddles<Mersenne31Complex, A>>,
    pub lde_precomputations: Arc<LdePrecomputations<A>>,
    pub setup: Arc<Vec<BF, B>>,
}

fn get_setup_from_row_major_trace<const N: usize, A: GoodAllocator, B: GoodAllocator>(trace: &RowMajorTrace<BF, N, A>) -> Arc<Vec<BF, B>>
{
    let mut setup_evaluations =
        Vec::with_capacity_in(trace.as_slice().len(), B::default());
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

impl<C: MachineConfig, A: GoodAllocator, B: GoodAllocator>
    From<MainCircuitPrecomputations<C, A, B>> for CircuitPrecomputationsHost<A, B>
{
    fn from(precomputations: MainCircuitPrecomputations<C, A, B>) -> Self {
        let MainCircuitPrecomputations {
            compiled_circuit,
            twiddles,
            lde_precomputations,
            setup,
            ..
        } = precomputations;
        CircuitPrecomputationsHost {
            compiled_circuit: Arc::new(compiled_circuit),
            twiddles: Arc::new(twiddles),
            lde_precomputations: Arc::new(lde_precomputations),
            setup: get_setup_from_row_major_trace(&setup.ldes[0].trace),
        }
    }
}

impl<A: GoodAllocator, B: GoodAllocator>
From<DelegationCircuitPrecomputations<A, B>> for CircuitPrecomputationsHost<A, B>
{
    fn from(precomputations: DelegationCircuitPrecomputations<A, B>) -> Self {
        let DelegationCircuitPrecomputations {
            compiled_circuit,
            twiddles,
            lde_precomputations,
            setup,
            ..
        } = precomputations;
        CircuitPrecomputationsHost {
            compiled_circuit: Arc::new(compiled_circuit.compiled_circuit),
            twiddles: Arc::new(twiddles),
            lde_precomputations: Arc::new(lde_precomputations),
            setup: get_setup_from_row_major_trace(&setup.ldes[0].trace),
        }
    }
}

