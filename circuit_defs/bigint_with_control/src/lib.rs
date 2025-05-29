#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use prover::cs;
use prover::cs::cs::witness_placer::graph_description::RawExpression;
use prover::fft::GoodAllocator;
use prover::field::Mersenne31Field;
use prover::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
use prover::*;

pub const DELEGATION_TYPE_ID: u32 =
    risc_v_simulator::delegations::u256_ops_with_control::U256_OPS_WITH_CONTROL_ACCESS_ID;
pub const DOMAIN_SIZE: usize = 1 << 21;
pub const NUM_DELEGATION_CYCLES: usize = DOMAIN_SIZE - 1;
pub const LDE_FACTOR: usize = 2;
pub const LDE_SOURCE_COSETS: &[usize] = &[0, 1];
pub const TREE_CAP_SIZE: usize = 32;

fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub fn get_delegation_circuit() -> DelegationProcessorDescription {
    use crate::field::Mersenne31Field;
    use cs::cs::circuit::Circuit;
    use cs::cs::cs_reference::BasicAssembly;
    use cs::delegation::bigint_with_control::define_u256_ops_extended_control_delegation_circuit;
    use cs::one_row_compiler::OneRowCompiler;

    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    define_u256_ops_extended_control_delegation_circuit(&mut cs);
    let (circuit_output, _) = cs.finalize();
    let table_driver = circuit_output.table_driver.clone();
    let compiler = OneRowCompiler::default();
    let circuit = compiler
        .compile_to_evaluate_delegations(circuit_output, DOMAIN_SIZE.trailing_zeros() as usize);

    let description = DelegationProcessorDescription {
        delegation_type: DELEGATION_TYPE_ID,
        num_requests_per_circuit: NUM_DELEGATION_CYCLES,
        trace_len: DOMAIN_SIZE,
        table_driver,
        compiled_circuit: circuit,
    };

    description
}

pub fn get_ssa_form() -> Vec<Vec<RawExpression<Mersenne31Field>>> {
    use crate::field::Mersenne31Field;
    use cs::cs::circuit::Circuit;
    use cs::cs::cs_reference::BasicAssembly;
    use cs::cs::witness_placer::graph_description::WitnessGraphCreator;
    use cs::delegation::bigint_with_control::define_u256_ops_extended_control_delegation_circuit;

    let mut cs = BasicAssembly::<Mersenne31Field, WitnessGraphCreator<Mersenne31Field>>::new();
    cs.witness_placer = Some(WitnessGraphCreator::<Mersenne31Field>::new());
    define_u256_ops_extended_control_delegation_circuit(&mut cs);

    let witness_placer = cs.witness_placer.unwrap();
    let (_resolution_order, ssa_forms) = witness_placer.compute_resolution_order();

    ssa_forms
}

pub fn get_table_driver() -> prover::cs::tables::TableDriver<Mersenne31Field> {
    use cs::delegation::bigint_with_control::u256_ops_extended_control_delegation_circuit_create_table_driver;
    u256_ops_extended_control_delegation_circuit_create_table_driver()
}

mod sealed {
    use crate::Mersenne31Field;
    use prover::cs::cs::witness_placer::*;
    use prover::witness_proxy::WitnessProxy;

    include!("../generated/witness_generation_fn.rs");
}

pub fn witness_eval_fn_for_gpu_tracer<'a, 'b>(
    proxy: &'_ mut SimpleWitnessProxy<'a, DelegationCircuitOracle<'b, impl GoodAllocator>>,
) {
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    let fn_ptr = sealed::evaluate_witness_fn::<
        ScalarWitnessTypeSet<Mersenne31Field, true>,
        SimpleWitnessProxy<'a, DelegationCircuitOracle<'b, _>>,
    >;
    (fn_ptr)(proxy);
}

pub fn generate_artifacts() {
    use std::io::Write;

    let compiled_circuit = get_delegation_circuit();
    serialize_to_file(&compiled_circuit.compiled_circuit, "generated/layout");

    let compiled_circuit = get_delegation_circuit();
    let (layout, quotient) =
        verifier_generator::generate_for_description(compiled_circuit.compiled_circuit);

    let mut dst = std::fs::File::create("generated/circuit_layout.rs").unwrap();
    dst.write_all(&layout.as_bytes()).unwrap();

    let mut dst = std::fs::File::create("generated/quotient.rs").unwrap();
    dst.write_all(&quotient.as_bytes()).unwrap();
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn generate() {
        generate_artifacts();
    }
}
