use super::*;
use crate::constraint::Constraint;
use crate::cs::circuit::*;
use crate::cs::circuit_trait::MemoryAccess;
use crate::oracle::Placeholder;
use crate::tables::TableDriver;
use field::PrimeField;
use std::collections::{BTreeMap, HashMap};

pub struct CircuitOutput<F: PrimeField> {
    pub table_driver: TableDriver<F>,
    pub num_of_variables: usize,
    pub constraints: Vec<(Constraint<F>, bool)>,
    pub lookups: Vec<LookupQuery<F>>,
    pub memory_queries: Vec<MemoryAccess>,
    pub register_and_indirect_memory_accesses: Vec<RegisterAndIndirectAccesses>,
    pub executor_machine_state: Option<OpcodeFamilyCircuitState<F>>,
    pub delegation_circuit_state: Option<DelegationCircuitState>,
    pub range_check_expressions: Vec<RangeCheckQuery<F>>,
    pub boolean_vars: Vec<Variable>,
    pub substitutions: HashMap<(Placeholder, usize), Variable>,
    pub variable_names: HashMap<Variable, String>,
    pub variables_from_constraints: BTreeMap<Variable, Constraint<F>>,
    pub layers_mapping: HashMap<Variable, usize>,
    pub circuit_family_bitmask: Vec<Variable>,
}

impl<F: PrimeField> CircuitOutput<F> {
    pub fn get_variable_by_placeholder(
        &self,
        placeholder: Placeholder,
        subindex: usize,
    ) -> Variable {
        self.substitutions
            .get(&(placeholder, subindex))
            .cloned()
            .unwrap()
    }
}
