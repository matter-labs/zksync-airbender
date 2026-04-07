use super::*;

pub fn evaluate_init_and_teardown_memory_witness<
    F: PrimeField,
    A: Allocator + Clone,
    B: Allocator + Clone,
>(
    dumped_inits_and_teardowns: Vec<([Vec<F, A>; 2], [Vec<F, A>; 2])>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    inner_allocator: A,
    outer_allocator: B,
) -> Vec<Vec<F, A>, B> {
    let mut result =
        Vec::with_capacity_in(compiled_circuit.memory_layout.total_width, outer_allocator);
    for _ in 0..compiled_circuit.memory_layout.total_width {
        result.push(Vec::new_in(inner_allocator.clone()));
    }

    assert_eq!(
        compiled_circuit.memory_layout.teardown_sets.len(),
        dumped_inits_and_teardowns.len()
    );
    for (set, desc) in dumped_inits_and_teardowns
        .into_iter()
        .zip(compiled_circuit.memory_layout.teardown_sets.iter())
    {
        let ([a_src, b_src], [c_src, d_src]) = set;
        let ([a, b], [c, d]) = desc;
        for (src, dest) in [(a_src, *a), (b_src, *b), (c_src, *c), (d_src, *d)] {
            let GKRAddress::BaseLayerMemory(dest) = dest else {
                unreachable!()
            };
            let t = core::mem::replace(&mut result[dest], src);
            assert!(t.is_empty());
        }
    }

    for el in result.iter() {
        assert!(el.is_empty() == false);
    }

    result
}
