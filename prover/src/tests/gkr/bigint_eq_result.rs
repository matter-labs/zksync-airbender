use super::bigint_with_extended_control::witness_eval_fn;
use super::orchestration::common::ensure_memory_trace_consistency;
use super::{deserialize_from_file, read_cell};
use crate::gkr::witness_gen::delegation_circuits::{
    evaluate_gkr_memory_witness_for_delegation_circuit, evaluate_gkr_witness_for_delegation_circuit,
};
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use crate::tracers::oracles::transpiler_oracles::delegation::BigintDelegationOracle;
use ::cs::definitions::gkr::{RamAddress, RamQuery, RamWordRepresentation};
use ::cs::definitions::GKRAddress;
use ::cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn;
use ::cs::gkr_compiler::{CompiledMaxQuadraticGKRRelation, GKRCircuitArtifact, GKRRelation};
use ::cs::tables::TableDriver;
use ::field::baby_bear::base::BabyBearField;
use ::field::{Field, PrimeField};
use common_constants::bigint_with_control::*;
use common_constants::rom::ROM_BYTE_SIZE;
use common_constants::{TimestampData, TimestampScalar, DELEGATION_INVOCATION_OFFSET};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::{RegisterOrIndirectReadData, RegisterOrIndirectReadWriteData};
use std::alloc::Global;
use std::sync::OnceLock;
use worker::Worker;

type F = BabyBearField;
type Trace = GKRFullWitnessTrace<F, Global, Global>;
type Relation = CompiledMaxQuadraticGKRRelation<F>;
type Word = [u32; 8];

const VARIANTS: [&str; 2] = ["layout_gkr", "layout_no_caches_gkr"];
const EQUALITY_FLAG_NAME: &str = "values are equal for perform eq";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Class {
    EqEqual,
    EqUnequal,
    OffEq,
}

struct Call {
    control: u32,
    a: Word,
    b: Word,
    class: Class,
}

fn word(low: u64) -> Word {
    let mut w = [0u32; 8];
    w[0] = low as u32;
    w[1] = (low >> 32) as u32;
    w
}

fn add(a: Word, b: Word) -> (Word, bool) {
    let mut r = [0u32; 8];
    let mut carry = 0u64;
    for i in 0..8 {
        let t = a[i] as u64 + b[i] as u64 + carry;
        r[i] = t as u32;
        carry = t >> 32;
    }
    (r, carry != 0)
}

fn sub(a: Word, b: Word) -> (Word, bool) {
    let mut r = [0u32; 8];
    let mut borrow = 0i64;
    for i in 0..8 {
        let t = a[i] as i64 - b[i] as i64 - borrow;
        r[i] = t as u32;
        borrow = (t < 0) as i64;
    }
    (r, borrow != 0)
}

fn mul(a: Word, b: Word) -> [u32; 16] {
    let mut r = [0u64; 16];
    for i in 0..8 {
        let mut carry = 0u64;
        for j in 0..8 {
            let t = a[i] as u64 * b[j] as u64 + r[i + j] + carry;
            r[i + j] = t & 0xffff_ffff;
            carry = t >> 32;
        }
        r[i + 8] = carry;
    }
    r.map(|limb| limb as u32)
}

fn execute(call: &Call) -> (Word, u32) {
    let (result, flag) = match call.control.trailing_zeros() as usize {
        ADD_OP_BIT_IDX => add(call.a, call.b),
        SUB_OP_BIT_IDX => sub(call.a, call.b),
        SUB_AND_NEGATE_OP_BIT_IDX => sub(call.b, call.a),
        MUL_LOW_OP_BIT_IDX => {
            let product = mul(call.a, call.b);
            (
                product[..8].try_into().unwrap(),
                product[8..].iter().any(|&limb| limb != 0),
            )
        }
        MUL_HIGH_OP_BIT_IDX => (mul(call.a, call.b)[8..].try_into().unwrap(), false),
        EQ_OP_BIT_IDX => (call.a, call.a == call.b),
        MEMCOPY_BIT_IDX => (call.b, false),
        _ => unreachable!(),
    };
    (result, flag as u32)
}

fn calls() -> Vec<Call> {
    let all_ones = [u32::MAX; 8];
    let mut top_bit = [0u32; 8];
    top_bit[7] = 1 << 31;
    let operand = [
        0x8765_4321,
        0x0fed_cba9,
        7,
        0,
        0xdead_beef,
        1,
        0,
        0x1234_5678,
    ];
    let call = |bit: usize, a: Word, b: Word, class: Class| Call {
        control: 1 << bit,
        a,
        b,
        class,
    };
    vec![
        call(ADD_OP_BIT_IDX, word(5), word(9), Class::OffEq),
        call(ADD_OP_BIT_IDX, all_ones, word(1), Class::OffEq),
        call(SUB_OP_BIT_IDX, word(1), word(2), Class::OffEq),
        call(SUB_AND_NEGATE_OP_BIT_IDX, word(1), word(5), Class::OffEq),
        call(MEMCOPY_BIT_IDX, word(3), operand, Class::OffEq),
        call(MUL_LOW_OP_BIT_IDX, top_bit, word(2), Class::OffEq),
        call(MUL_HIGH_OP_BIT_IDX, operand, operand, Class::OffEq),
        call(EQ_OP_BIT_IDX, operand, operand, Class::EqEqual),
        call(EQ_OP_BIT_IDX, word(5), word(3), Class::EqUnequal),
        call(EQ_OP_BIT_IDX, word(3), word(5), Class::EqUnequal),
    ]
}

fn witness_row(index: usize, call: &Call) -> (BigintDelegationWitness, u32) {
    let (result, x12_out) = execute(call);
    let write_timestamp: TimestampScalar =
        (1 << 24) + 16 * index as TimestampScalar + DELEGATION_INVOCATION_OFFSET;
    let read_timestamp = TimestampData::from_scalar(write_timestamp - 5);
    let a_ptr = ROM_BYTE_SIZE as u32 + 128 * index as u32;
    let b_ptr = a_ptr + 64;

    let mut row = BigintDelegationWitness::empty();
    row.write_timestamp = write_timestamp;
    row.reg_accesses[0] = RegisterOrIndirectReadWriteData {
        read_value: a_ptr,
        write_value: a_ptr,
        timestamp: read_timestamp,
    };
    row.reg_accesses[1] = RegisterOrIndirectReadWriteData {
        read_value: b_ptr,
        write_value: b_ptr,
        timestamp: read_timestamp,
    };
    row.reg_accesses[2] = RegisterOrIndirectReadWriteData {
        read_value: call.control,
        write_value: x12_out,
        timestamp: read_timestamp,
    };
    for i in 0..8 {
        row.indirect_reads[i] = RegisterOrIndirectReadData {
            read_value: call.b[i],
            timestamp: read_timestamp,
        };
        row.indirect_writes[i] = RegisterOrIndirectReadWriteData {
            read_value: call.a[i],
            write_value: result[i],
            timestamp: read_timestamp,
        };
    }
    (row, x12_out)
}

struct Fixture {
    circuit: GKRCircuitArtifact<F>,
    trace: Trace,
    calls: Vec<Call>,
    x12_results: Vec<u32>,
    x12_low: GKRAddress,
    equality_flag: GKRAddress,
}

impl Fixture {
    fn new(variant: &str) -> Self {
        let circuit: GKRCircuitArtifact<F> = deserialize_from_file(&format!(
            "../cs/compiled_circuits/bigint_with_extended_control_{variant}.json"
        ));
        let calls = calls();
        let (rows, x12_results): (Vec<_>, Vec<_>) = calls
            .iter()
            .enumerate()
            .map(|(index, call)| witness_row(index, call))
            .unzip();
        let oracle = BigintDelegationOracle {
            cycle_data: &rows,
            marker: core::marker::PhantomData,
        };
        let mut table_driver = TableDriver::<F>::new();
        bigint_with_extended_control_delegation_circuit_table_driver_fn(&mut table_driver);
        let worker = Worker::new();
        let memory = evaluate_gkr_memory_witness_for_delegation_circuit(
            &circuit,
            circuit.trace_len,
            &oracle,
            &worker,
            Global,
            Global,
        );
        let trace = evaluate_gkr_witness_for_delegation_circuit(
            &circuit,
            witness_eval_fn,
            circuit.trace_len,
            &oracle,
            &table_driver,
            &worker,
            Global,
            Global,
        );
        ensure_memory_trace_consistency(&memory, &trace);

        let x12_low = circuit
            .memory_layout
            .ram_access_sets
            .iter()
            .find_map(|query| match query {
                RamQuery::Write(write) if write.address == RamAddress::ConstantRegister(12) => {
                    match write.write_value {
                        RamWordRepresentation::U16Limbs([low, _]) => {
                            Some(GKRAddress::BaseLayerMemory(low))
                        }
                        _ => None,
                    }
                }
                _ => None,
            })
            .expect("x12 write access");
        let equality_flags: Vec<_> = circuit
            .variable_names
            .iter()
            .filter(|(_, name)| name.as_str() == EQUALITY_FLAG_NAME)
            .map(|(variable, _)| circuit.placement_data[variable])
            .collect();
        assert_eq!(equality_flags.len(), 1);

        Self {
            circuit,
            trace,
            calls,
            x12_results,
            x12_low,
            equality_flag: equality_flags[0],
        }
    }

    fn padding_row(&self) -> usize {
        self.calls.len()
    }

    fn rows_of(&self, class: Class) -> Vec<usize> {
        let rows: Vec<_> = (0..self.calls.len())
            .filter(|&row| self.calls[row].class == class)
            .collect();
        assert!(!rows.is_empty());
        rows
    }

    fn relations(&self) -> Vec<&Relation> {
        let relations: Vec<&Relation> = self
            .circuit
            .layers
            .iter()
            .flat_map(|layer| {
                layer
                    .gates_with_external_connections
                    .iter()
                    .chain(layer.gates.iter())
            })
            .filter_map(|gate| match &gate.enforced_relation {
                GKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => Some(input),
                _ => None,
            })
            .collect();
        assert_eq!(
            relations.len(),
            self.circuit.degree_1_constraints.len() + self.circuit.degree_2_constraints.len()
        );
        relations
    }

    /// The single relation with a linear term on `column`; all its inputs are committed columns,
    /// so evaluating it on a mutated row reads no stale intermediate copy.
    fn defining_relation(&self, column: GKRAddress) -> &Relation {
        let found: Vec<_> = self
            .relations()
            .into_iter()
            .filter(|relation| relation.linear_terms.iter().any(|(_, a)| *a == column))
            .collect();
        assert_eq!(found.len(), 1, "{column:?}");
        assert!(inputs(found[0]).iter().all(|address| matches!(
            address,
            GKRAddress::BaseLayerWitness(_) | GKRAddress::BaseLayerMemory(_)
        )));
        found[0]
    }

    fn x12_relation(&self) -> &Relation {
        self.defining_relation(self.x12_low)
    }

    fn equality_flag_relation(&self) -> &Relation {
        self.defining_relation(self.equality_flag)
    }

    fn cell(&self, address: GKRAddress, row: usize) -> F {
        match address {
            GKRAddress::BaseLayerWitness(_) | GKRAddress::BaseLayerMemory(_) => {
                read_cell(&self.trace, address, row)
            }
            _ => {
                self.trace.column_major_scratch_space_trace
                    [self.circuit.scratch_space_mapping[&address]][row]
            }
        }
    }

    fn holds(&self, relation: &Relation, row: usize, overrides: &[(GKRAddress, F)]) -> bool {
        evaluate(relation, |address| {
            overrides
                .iter()
                .find(|(a, _)| *a == address)
                .map(|(_, value)| *value)
                .unwrap_or_else(|| self.cell(address, row))
        }) == F::ZERO
    }
}

fn fixtures() -> &'static [Fixture; 2] {
    static FIXTURES: OnceLock<[Fixture; 2]> = OnceLock::new();
    FIXTURES.get_or_init(|| VARIANTS.map(|variant| Fixture::new(variant)))
}

fn inputs(relation: &Relation) -> Vec<GKRAddress> {
    relation
        .quadratic_terms
        .iter()
        .flat_map(|(a, terms)| std::iter::once(*a).chain(terms.iter().map(|(_, b)| *b)))
        .chain(relation.linear_terms.iter().map(|(_, a)| *a))
        .collect()
}

fn evaluate(relation: &Relation, value: impl Fn(GKRAddress) -> F) -> F {
    let mut result = relation.constant;
    for (a, terms) in relation.quadratic_terms.iter() {
        let mut inner = F::ZERO;
        for (coefficient, b) in terms.iter() {
            let mut term = *coefficient;
            term.mul_assign(&value(*b));
            inner.add_assign(&term);
        }
        inner.mul_assign(&value(*a));
        result.add_assign(&inner);
    }
    for (coefficient, a) in relation.linear_terms.iter() {
        let mut term = *coefficient;
        term.mul_assign(&value(*a));
        result.add_assign(&term);
    }
    result
}

fn flipped(value: F) -> F {
    if value == F::ZERO {
        F::ONE
    } else {
        F::ZERO
    }
}

#[test]
fn bigint_honest_trace_satisfies_the_lowered_relations() {
    for fixture in fixtures() {
        let relations = fixture.relations();
        for row in 0..fixture.circuit.trace_len {
            assert!(
                relations
                    .iter()
                    .all(|relation| fixture.holds(relation, row, &[])),
                "row {row}"
            );
        }
        assert!(fixture.x12_results.contains(&1) && fixture.x12_results.contains(&0));
        for (row, call) in fixture.calls.iter().enumerate() {
            let x12 = fixture.cell(fixture.x12_low, row).as_u32_reduced();
            assert_eq!(x12, fixture.x12_results[row], "row {row}");
            match call.class {
                Class::EqEqual => assert_eq!(x12, 1),
                Class::EqUnequal => assert_eq!(x12, 0),
                Class::OffEq => {}
            }
        }
        assert!(fixture
            .rows_of(Class::OffEq)
            .iter()
            .any(|&row| fixture.x12_results[row] == 1));
        let padding = fixture.padding_row();
        assert_eq!(fixture.cell(fixture.x12_low, padding), F::ZERO);
        assert_eq!(fixture.cell(fixture.equality_flag, padding), F::ONE);
    }
}

#[test]
fn bigint_eq_cannot_claim_equality_of_unequal_operands() {
    for fixture in fixtures() {
        for row in fixture.rows_of(Class::EqUnequal) {
            assert_eq!(fixture.cell(fixture.equality_flag, row), F::ZERO);
            let forged_result = [(fixture.x12_low, F::ONE)];
            assert!(!fixture.holds(fixture.x12_relation(), row, &forged_result));
            let forged_result_and_flag =
                [(fixture.x12_low, F::ONE), (fixture.equality_flag, F::ONE)];
            assert!(fixture.holds(fixture.x12_relation(), row, &forged_result_and_flag));
            assert!(!fixture.holds(
                fixture.equality_flag_relation(),
                row,
                &forged_result_and_flag
            ));
        }
    }
}

#[test]
fn bigint_eq_cannot_deny_equality_of_equal_operands() {
    for fixture in fixtures() {
        for row in fixture.rows_of(Class::EqEqual) {
            assert_eq!(fixture.cell(fixture.equality_flag, row), F::ONE);
            let forged_result = [(fixture.x12_low, F::ZERO)];
            assert!(!fixture.holds(fixture.x12_relation(), row, &forged_result));
            let forged_result_and_flag =
                [(fixture.x12_low, F::ZERO), (fixture.equality_flag, F::ZERO)];
            assert!(!fixture.holds(
                fixture.equality_flag_relation(),
                row,
                &forged_result_and_flag
            ));
        }
    }
}

#[test]
fn bigint_equality_flag_contributes_nothing_off_eq_rows() {
    for fixture in fixtures() {
        let mut rows = fixture.rows_of(Class::OffEq);
        rows.push(fixture.padding_row());
        for row in rows {
            let flag = fixture.cell(fixture.equality_flag, row);
            let forged_flag = [(fixture.equality_flag, flipped(flag))];
            assert!(
                fixture.holds(fixture.x12_relation(), row, &forged_flag),
                "row {row}"
            );
            assert!(
                !fixture.holds(fixture.equality_flag_relation(), row, &forged_flag),
                "row {row}"
            );
            let result = fixture.cell(fixture.x12_low, row);
            let forged_result = [(fixture.x12_low, flipped(result))];
            assert!(
                !fixture.holds(fixture.x12_relation(), row, &forged_result),
                "row {row}"
            );
        }
    }
}
