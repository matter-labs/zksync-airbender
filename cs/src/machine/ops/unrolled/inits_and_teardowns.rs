use super::*;

pub fn inits_and_teardowns_tables() -> Vec<TableType> {
    vec![]
}

pub fn inits_and_teardowns_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in inits_and_teardowns_tables() {
        cs.materialize_table(el);
    }
}

pub fn inits_and_teardowns_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in inits_and_teardowns_tables() {
        table_driver.materialize_table(el);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::one_row_compiler::OneRowCompiler;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_inits_and_teardowns_circuit() {
        use ::field::Mersenne31Field;

        let compiler = OneRowCompiler::<Mersenne31Field>::default();
        let compiled = compiler.compile_init_and_teardown_circuit(16, 24);

        serialize_to_file(&compiled, "inits_and_teardowns_preprocessed_layout.json");
    }

    #[test]
    fn compile_inits_and_teardowns_witness_graph() {
        use ::field::Mersenne31Field;

        let graph = WitnessGraphCreator::<Mersenne31Field>::new();
        let (_, ssa_forms) = graph.compute_resolution_order();

        serialize_to_file(&ssa_forms, "inits_and_teardowns_preprocessed_ssa.json");
    }
}
