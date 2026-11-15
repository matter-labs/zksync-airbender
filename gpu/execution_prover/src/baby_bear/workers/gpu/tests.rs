use super::*;
use gpu_trace::witness::circuit_type::UnrolledCircuitType;

fn tagged_partial_trees(circuit_type: CircuitType, profile: ProofProfile) -> MemoryPartialTrees {
    MemoryPartialTrees {
        layout_version: gpu_trace::baby_bear::trace::memory_cap::PARTIAL_TREES_LAYOUT_VERSION,
        circuit_type,
        profile,
        log_domain_size: 22,
        log_lde_factor: 4,
        log_rows_per_leaf: 1,
        log_tree_cap_size: 4,
        reduction_layers: 10,
        columns_count: 104,
        nodes: execution_prover_model::allocator::PooledHostBuffer::new(
            vec![[7; 8]; 3],
            crossbeam_channel::unbounded().0,
        ),
    }
}

const UNIFIED: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified);
const UNIFIED22: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified22);

#[test]
#[should_panic(
    expected = "Unrolled(Unified22)/CompressionFinal proof requires the memory partial trees persisted by its commitment"
)]
fn cpu_compression_proof_without_partial_trees_panics() {
    proof_partial_trees::<std::alloc::Global>(UNIFIED22, ProofProfile::CompressionFinal, None);
}

#[test]
#[should_panic(expected = "Unrolled(Unified)/Standard proof does not take memory partial trees")]
fn cpu_standard_proof_with_partial_trees_panics() {
    proof_partial_trees(
        UNIFIED,
        ProofProfile::Standard,
        Some(tagged_partial_trees(UNIFIED, ProofProfile::Standard)),
    );
}

#[test]
#[should_panic(expected = "memory partial trees belong to another circuit or profile")]
fn cpu_partial_trees_of_another_circuit_panic() {
    proof_partial_trees(
        UNIFIED22,
        ProofProfile::CompressionFinal,
        Some(tagged_partial_trees(
            UNIFIED,
            ProofProfile::CompressionFinal,
        )),
    );
}
