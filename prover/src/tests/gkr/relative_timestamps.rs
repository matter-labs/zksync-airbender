use super::orchestration::common::{run_vm_and_capture, ProgramConfig, VmRunOutput};
use super::{
    check_satisfied, deserialize_from_file, parse_delegation_ram_accesses_from_full_trace,
    read_cell, write_cell,
};
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::delegation_circuits::{
    evaluate_gkr_memory_witness_for_delegation_circuit, evaluate_gkr_witness_for_delegation_circuit,
};
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use crate::tracers::oracles::transpiler_oracles::delegation::DelegationOracle;
use ::cs::definitions::gkr::RelativeTimestampGroup;
use ::cs::definitions::GKRAddress;
use ::cs::gkr_compiler::{CompiledMaxQuadraticGKRRelation, GKRCircuitArtifact, GKRRelation};
use ::cs::tables::TableDriver;
use ::field::baby_bear::base::BabyBearField;
use ::field::{Field, PrimeField};
use common_constants::keccak_f1600::*;
use common_constants::{
    TimestampData, TimestampScalar, ROM_SECOND_WORD_BITS, TIMESTAMP_COLUMNS_NUM_BITS,
};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{DelegationsAndFamiliesCounters, ReplayBuffer};
use riscv_transpiler::witness::delegation::keccak_f1600::{
    KeccakChi5AbiDescription, KeccakColumnParityAbiDescription, KeccakThetaRhoAbiDescription,
};
use riscv_transpiler::witness::delegation::DelegationAbiDescription;
use riscv_transpiler::witness::{DelegationDestinationHolder, DelegationWitness};
use std::alloc::Global;
use std::collections::{BTreeMap, BTreeSet};
use worker::Worker;

type F = BabyBearField;
type Trace = GKRFullWitnessTrace<F, Global, Global>;
type Counters = DelegationsAndFamiliesCounters;
type Row<const IW: usize, const VO: usize> =
    DelegationWitness<NUM_KECCAK_F1600_REGISTER_ACCESSES, NUM_KECCAK_F1600_INDIRECT_READS, IW, VO>;

type Tuple = (bool, u32, TimestampScalar, u32);
type Tuples = BTreeSet<Tuple>;

const LIMB: TimestampScalar = 1 << TIMESTAMP_COLUMNS_NUM_BITS;
const VARIANTS: [&str; 2] = ["layout_gkr", "layout_no_caches_gkr"];

struct KeccakCircuit<D: DelegationAbiDescription, const IW: usize, const VO: usize> {
    stem: &'static str,
    table_driver_fn: fn(&mut TableDriver<F>),
    eval_fn: fn(
        &mut ColumnMajorWitnessProxy<
            '_,
            DelegationOracle<
                '_,
                D,
                NUM_KECCAK_F1600_REGISTER_ACCESSES,
                NUM_KECCAK_F1600_INDIRECT_READS,
                IW,
                VO,
            >,
            F,
        >,
    ),
    rows: Vec<Row<IW, VO>>,
}

impl<D: DelegationAbiDescription, const IW: usize, const VO: usize> KeccakCircuit<D, IW, VO> {
    fn artifact(&self, variant: &str) -> GKRCircuitArtifact<F> {
        deserialize_from_file(&format!(
            "../cs/compiled_circuits/{}_{variant}.json",
            self.stem
        ))
    }

    fn trace(&self, circuit: &GKRCircuitArtifact<F>, rows: &[Row<IW, VO>]) -> Trace {
        let mut table_driver = TableDriver::<F>::new();
        (self.table_driver_fn)(&mut table_driver);
        let oracle = DelegationOracle::<
            '_,
            D,
            NUM_KECCAK_F1600_REGISTER_ACCESSES,
            NUM_KECCAK_F1600_INDIRECT_READS,
            IW,
            VO,
        > {
            cycle_data: rows,
            marker: core::marker::PhantomData,
        };
        evaluate_gkr_witness_for_delegation_circuit(
            circuit,
            self.eval_fn,
            circuit.trace_len,
            &oracle,
            &table_driver,
            &Worker::new(),
            Global,
            Global,
        )
    }

    fn tuples(&self, rows: &[Row<IW, VO>]) -> (Tuples, Tuples) {
        let circuit = self.artifact(VARIANTS[0]);
        let oracle = DelegationOracle::<
            '_,
            D,
            NUM_KECCAK_F1600_REGISTER_ACCESSES,
            NUM_KECCAK_F1600_INDIRECT_READS,
            IW,
            VO,
        > {
            cycle_data: rows,
            marker: core::marker::PhantomData,
        };
        let memory = evaluate_gkr_memory_witness_for_delegation_circuit(
            &circuit,
            circuit.trace_len,
            &oracle,
            &Worker::new(),
            Global,
            Global,
        );
        let (mut writes, mut reads, mut delegations) =
            (BTreeSet::new(), BTreeSet::new(), BTreeSet::new());
        parse_delegation_ram_accesses_from_full_trace(
            &circuit,
            &memory,
            &mut writes,
            &mut reads,
            &mut delegations,
            D::DELEGATION_TYPE,
        );
        assert_eq!(delegations.len(), rows.len());
        (writes, reads)
    }

    fn retimed(&self, retime: impl Fn(&Row<IW, VO>) -> Option<Row<IW, VO>>) -> Vec<Row<IW, VO>> {
        self.rows.iter().filter_map(retime).collect()
    }
}

fn replay<const CSR: u16, const IW: usize, const VO: usize>(
    vm: &VmRunOutput<Counters>,
    num_calls: usize,
) -> Vec<Row<IW, VO>> {
    let mut rows = vec![DelegationWitness::empty(); num_calls];
    {
        let mut state = vm.snapshotter.initial_snapshot.state;
        let mut ram_log = vm
            .snapshotter
            .reads_buffer
            .make_range(0..vm.snapshotter.reads_buffer.len());
        let mut ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log,
        };
        let mut buffers = vec![&mut rows[..]];
        let mut tracer = DelegationDestinationHolder::<
            '_,
            CSR,
            NUM_KECCAK_F1600_REGISTER_ACCESSES,
            NUM_KECCAK_F1600_INDIRECT_READS,
            IW,
            VO,
        > {
            buffers: &mut buffers[..],
        };
        ReplayerVM::<Counters>::replay_basic_unrolled::<_, _, F>(
            &mut state,
            &mut ram,
            &vm.tape,
            &mut (),
            vm.cycles_bound,
            &mut tracer,
        );
        assert_eq!(vm.expected_final_state(), state);
    }
    rows
}

fn theta_rho(
    vm: &VmRunOutput<Counters>,
) -> KeccakCircuit<
    KeccakThetaRhoAbiDescription,
    KECCAK_THETA_RHO_X11_NUM_WRITES,
    KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
> {
    let permutations = keccak_f1600_permutations(vm.counters.keccak_f1600_calls);
    assert!(permutations > 0);
    KeccakCircuit {
        stem: "keccak_theta_rho",
        table_driver_fn: ::cs::gkr_circuits::delegation::keccak_theta_rho::keccak_theta_rho_delegation_circuit_table_driver_fn,
        eval_fn: super::keccak_theta_rho::witness_eval_fn,
        rows: replay::<{ KECCAK_THETA_RHO_CSR_REGISTER as u16 }, _, _>(
            vm,
            permutations * NUM_KECCAK_F1600_THETA_RHO_CALLS,
        ),
    }
}

fn chi5(
    vm: &VmRunOutput<Counters>,
) -> KeccakCircuit<
    KeccakChi5AbiDescription,
    KECCAK_CHI5_X11_NUM_WRITES,
    KECCAK_CHI5_NUM_VARIABLE_OFFSETS,
> {
    let permutations = keccak_f1600_permutations(vm.counters.keccak_f1600_calls);
    assert!(permutations > 0);
    KeccakCircuit {
        stem: "keccak_chi5",
        table_driver_fn:
            ::cs::gkr_circuits::delegation::keccak_chi5::keccak_chi5_delegation_circuit_table_driver_fn,
        eval_fn: super::keccak_chi5::witness_eval_fn,
        rows: replay::<{ KECCAK_CHI5_CSR_REGISTER as u16 }, _, _>(
            vm,
            permutations * NUM_KECCAK_F1600_CHI5_CALLS,
        ),
    }
}

fn column_parity(
    vm: &VmRunOutput<Counters>,
) -> KeccakCircuit<
    KeccakColumnParityAbiDescription,
    KECCAK_COLUMN_PARITY_X11_NUM_WRITES,
    KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS,
> {
    let permutations = keccak_f1600_permutations(vm.counters.keccak_f1600_calls);
    assert!(permutations > 0);
    KeccakCircuit {
        stem: "keccak_column_parity",
        table_driver_fn: ::cs::gkr_circuits::delegation::keccak_column_parity::keccak_column_parity_delegation_circuit_table_driver_fn,
        eval_fn: super::keccak_column_parity::witness_eval_fn,
        rows: replay::<{ KECCAK_COLUMN_PARITY_CSR_REGISTER as u16 }, _, _>(
            vm,
            permutations * NUM_KECCAK_F1600_COLUMN_PARITY_CALLS,
        ),
    }
}

fn keccak_vm() -> VmRunOutput<Counters> {
    run_vm_and_capture::<Counters, FullUnsignedMachineDecoderConfig>(
        &ProgramConfig::keccak(),
        &Worker::new(),
    )
}

fn addresses(group: &RelativeTimestampGroup) -> [GKRAddress; 3] {
    [
        GKRAddress::BaseLayerMemory(group.read_timestamp[0]),
        GKRAddress::BaseLayerMemory(group.read_timestamp[1]),
        GKRAddress::BaseLayerWitness(group.borrow),
    ]
}

type Relation = CompiledMaxQuadraticGKRRelation<F>;

fn lowered_constraints(circuit: &GKRCircuitArtifact<F>) -> Vec<&Relation> {
    let constraints: Vec<&Relation> = circuit
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
        constraints.len(),
        circuit.degree_1_constraints.len() + circuit.degree_2_constraints.len()
    );
    constraints
}

fn inputs(relation: &Relation) -> BTreeSet<GKRAddress> {
    relation
        .quadratic_terms
        .iter()
        .flat_map(|(a, terms)| std::iter::once(*a).chain(terms.iter().map(|(_, b)| *b)))
        .chain(relation.linear_terms.iter().map(|(_, a)| *a))
        .collect()
}

fn evaluate(relation: &Relation, trace: &Trace, row: usize) -> F {
    let mut result = relation.constant;
    for (a, terms) in relation.quadratic_terms.iter() {
        let mut inner = F::ZERO;
        for (coefficient, b) in terms.iter() {
            let mut term = *coefficient;
            term.mul_assign(&read_cell(trace, *b, row));
            inner.add_assign(&term);
        }
        inner.mul_assign(&read_cell(trace, *a, row));
        result.add_assign(&inner);
    }
    for (coefficient, a) in relation.linear_terms.iter() {
        let mut term = *coefficient;
        term.mul_assign(&read_cell(trace, *a, row));
        result.add_assign(&term);
    }
    result
}

fn failing(constraints: &[&Relation], trace: &Trace, row: usize) -> Vec<BTreeSet<GKRAddress>> {
    constraints
        .iter()
        .filter(|relation| evaluate(relation, trace, row) != F::ZERO)
        .map(|relation| inputs(relation))
        .collect()
}

fn lowered_constraints_hold(constraints: &[&Relation], trace: &Trace) -> bool {
    (0..trace.column_major_memory_trace[0].len())
        .all(|row| failing(constraints, trace, row).is_empty())
}

fn low_relation<'a>(constraints: &[&'a Relation], group: &RelativeTimestampGroup) -> &'a Relation {
    let [low, ..] = addresses(group);
    let mut relations = constraints
        .iter()
        .filter(|relation| inputs(relation).contains(&low));
    let relation = relations.next().unwrap();
    assert!(relations.next().is_none());
    relation
}

fn distance_inputs(
    circuit: &GKRCircuitArtifact<F>,
    constraints: &[&Relation],
    group: &RelativeTimestampGroup,
) -> Vec<GKRAddress> {
    let state = circuit.memory_layout.delegation_state.as_ref().unwrap();
    let [low, _, borrow] = addresses(group);
    let known = [
        low,
        GKRAddress::BaseLayerMemory(state.invocation_timestamp[0]),
        GKRAddress::BaseLayerMemory(state.execute),
        borrow,
    ];
    inputs(low_relation(constraints, group))
        .into_iter()
        .filter(|place| !known.contains(place))
        .collect()
}

fn tampered_failures(
    constraints: &[&Relation],
    trace: &mut Trace,
    row: usize,
    tampered: &[(GKRAddress, F)],
) -> Vec<BTreeSet<GKRAddress>> {
    let honest: Vec<F> = tampered
        .iter()
        .map(|(address, _)| read_cell(trace, *address, row))
        .collect();
    for (address, value) in tampered {
        write_cell(trace, *address, row, *value);
    }
    let result = failing(constraints, trace, row);
    for ((address, _), value) in tampered.iter().zip(honest) {
        write_cell(trace, *address, row, value);
    }
    result
}

fn rejected_with(
    constraints: &[&Relation],
    trace: &mut Trace,
    row: usize,
    tampered: &[(GKRAddress, F)],
    expected: GKRAddress,
) -> bool {
    tampered_failures(constraints, trace, row, tampered)
        .iter()
        .any(|inputs| inputs.contains(&expected))
}

fn plus(value: F, delta: u32) -> F {
    let mut value = value;
    value.add_assign(&F::from_u32_unchecked(delta));
    value
}

fn minus(value: F, delta: u32) -> F {
    let mut value = value;
    value.sub_assign(&F::from_u32_unchecked(delta));
    value
}

fn tampering_reaches_the_relations<
    D: DelegationAbiDescription,
    const IW: usize,
    const VO: usize,
>(
    circuit: &KeccakCircuit<D, IW, VO>,
) {
    let active = circuit.rows.len();
    for variant in VARIANTS {
        let artifact = circuit.artifact(variant);
        let constraints = lowered_constraints(&artifact);
        let groups = &artifact.aux_layout_data.relative_timestamp_groups;
        assert!(!groups.is_empty());
        let mut trace = circuit.trace(&artifact, &circuit.rows);
        assert!(lowered_constraints_hold(&constraints, &trace), "{variant}");
        for row in [0, active / 2, active - 1, active, artifact.trace_len - 1] {
            for group in groups.iter() {
                let [low, high, borrow] = addresses(group);
                let [l, h, b] = [low, high, borrow].map(|a| read_cell(&trace, a, row));
                let context = format!("{variant} row {row} group {:?}", group.members);
                assert!(
                    rejected_with(&constraints, &mut trace, row, &[(low, plus(l, 1))], low),
                    "{context}"
                );
                assert!(
                    rejected_with(&constraints, &mut trace, row, &[(high, plus(h, 1))], high),
                    "{context}"
                );
                assert!(
                    rejected_with(
                        &constraints,
                        &mut trace,
                        row,
                        &[(borrow, F::from_u32_unchecked(1 - b.as_u32_reduced()))],
                        low
                    ),
                    "{context}"
                );
                let lift = 2 - b.as_u32_reduced();
                assert_eq!(
                    tampered_failures(
                        &constraints,
                        &mut trace,
                        row,
                        &[
                            (low, plus(l, lift * LIMB as u32)),
                            (high, minus(h, lift)),
                            (borrow, F::from_u32_unchecked(2)),
                        ]
                    ),
                    vec![BTreeSet::from([borrow])],
                    "{context}: only booleanity rejects a borrow of 2"
                );
                if row < active {
                    for input in distance_inputs(&artifact, &constraints, group) {
                        let value = read_cell(&trace, input, row);
                        assert!(
                            rejected_with(
                                &constraints,
                                &mut trace,
                                row,
                                &[(input, plus(value, 1))],
                                low
                            ),
                            "{context} input {input:?}"
                        );
                    }
                    let other = if b == F::ZERO {
                        [
                            (low, plus(l, LIMB as u32)),
                            (high, minus(h, 1)),
                            (borrow, F::ONE),
                        ]
                    } else {
                        [
                            (low, minus(l, LIMB as u32)),
                            (high, plus(h, 1)),
                            (borrow, F::ZERO),
                        ]
                    };
                    assert!(
                        tampered_failures(&constraints, &mut trace, row, &other).is_empty(),
                        "{context}: the other limb pair of the same timestamp is left to the memory permutation"
                    );
                }
            }
        }
        assert!(lowered_constraints_hold(&constraints, &trace), "{variant}");
        assert!(check_satisfied(&artifact, &trace), "{variant}");
    }
}

fn shift<const IW: usize, const VO: usize>(row: &mut Row<IW, VO>, members: &[usize], delta: i64) {
    let shifted = |t: TimestampScalar| {
        let t = t as i64 + delta;
        assert!(t >= 0);
        t as TimestampScalar
    };
    for &member in members {
        let timestamp = if member < NUM_KECCAK_F1600_REGISTER_ACCESSES {
            &mut row.reg_accesses[member].timestamp
        } else {
            &mut row.indirect_writes[member - NUM_KECCAK_F1600_REGISTER_ACCESSES].timestamp
        };
        *timestamp = TimestampData::from_scalar(shifted(timestamp.as_scalar()));
    }
}

fn read_timestamp(trace: &Trace, group: &RelativeTimestampGroup, row: usize) -> TimestampScalar {
    let [low, high] = group.read_timestamp.map(|column| {
        trace.column_major_memory_trace[column][row].as_u32_reduced() as TimestampScalar
    });
    low + high * LIMB
}

fn borrows_follow_the_limb_boundaries<
    D: DelegationAbiDescription,
    const IW: usize,
    const VO: usize,
>(
    circuit: &KeccakCircuit<D, IW, VO>,
) -> BTreeSet<TimestampScalar> {
    let artifact = circuit.artifact(VARIANTS[0]);
    let top = LIMB - 1;
    let invocations: Vec<TimestampScalar> = [
        (0, 37),
        (0, 41),
        (0, LIMB - 3),
        (1, 1),
        (1, 5),
        (1, 13),
        (1, 21),
        (1, 33),
        (1, 37),
        (1, LIMB - 3),
        (top, 1),
        (top, 17),
        (top, LIMB - 3),
    ]
    .map(|(high, low)| high * LIMB + low)
    .to_vec();
    let rows: Vec<Row<IW, VO>> = invocations
        .iter()
        .flat_map(|&invocation| {
            circuit.rows.iter().map(move |row| {
                let delta = invocation as i64 - row.write_timestamp as i64;
                retime(row, delta, |_| delta)
            })
        })
        .collect();
    let trace = circuit.trace(&artifact, &rows);
    assert!(lowered_constraints_hold(
        &lowered_constraints(&artifact),
        &trace
    ));
    let mut distances = BTreeSet::new();
    let mut borrows = BTreeSet::new();
    for (row, witness) in rows.iter().enumerate() {
        let invocation = witness.write_timestamp;
        for group in artifact.aux_layout_data.relative_timestamp_groups.iter() {
            let read = read_timestamp(&trace, group, row);
            let distance = invocation + 2 - read;
            assert!(
                distance > 0 && distance < LIMB && distance % 4 == 0,
                "row {row}"
            );
            let borrow = trace.column_major_witness_trace[group.borrow][row].as_u32_reduced();
            assert_eq!(borrow == 1, (invocation % LIMB) + 2 < distance, "row {row}");
            borrows.insert(borrow);
            distances.insert(distance);
        }
    }
    assert_eq!(borrows, BTreeSet::from([0, 1]));
    distances
}

fn disagreeing_members_are_refused<
    D: DelegationAbiDescription,
    const IW: usize,
    const VO: usize,
>(
    circuit: &KeccakCircuit<D, IW, VO>,
) {
    let artifact = circuit.artifact(VARIANTS[0]);
    for group in artifact.aux_layout_data.relative_timestamp_groups.iter() {
        let mut rows = circuit.rows.clone();
        shift(&mut rows[5], &group.members[group.members.len() - 1..], 4);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            circuit.trace(&artifact, &rows)
        }));
        assert!(result.is_err(), "group {:?}", group.members);
    }
}

fn retime<const IW: usize, const VO: usize>(
    row: &Row<IW, VO>,
    invocation: i64,
    read: impl Fn(TimestampScalar) -> i64,
) -> Row<IW, VO> {
    let shifted = |t: TimestampScalar, delta: i64| {
        let t = t as i64 + delta;
        assert!(t >= 0);
        t as TimestampScalar
    };
    let mut row = *row;
    row.write_timestamp = shifted(row.write_timestamp, invocation);
    for timestamp in row
        .reg_accesses
        .iter_mut()
        .map(|access| &mut access.timestamp)
        .chain(
            row.indirect_writes
                .iter_mut()
                .map(|access| &mut access.timestamp),
        )
    {
        let t = timestamp.as_scalar();
        *timestamp = TimestampData::from_scalar(shifted(t, read(t)));
    }
    row
}

fn read_timestamps<const IW: usize, const VO: usize>(
    row: &Row<IW, VO>,
) -> impl Iterator<Item = TimestampScalar> + '_ {
    row.reg_accesses
        .iter()
        .map(|access| access.timestamp.as_scalar())
        .chain(
            row.indirect_writes
                .iter()
                .map(|access| access.timestamp.as_scalar()),
        )
}

type ColumnParity = KeccakCircuit<
    KeccakColumnParityAbiDescription,
    KECCAK_COLUMN_PARITY_X11_NUM_WRITES,
    KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS,
>;
type ThetaRho = KeccakCircuit<
    KeccakThetaRhoAbiDescription,
    KECCAK_THETA_RHO_X11_NUM_WRITES,
    KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
>;
type Chi5 = KeccakCircuit<
    KeccakChi5AbiDescription,
    KECCAK_CHI5_X11_NUM_WRITES,
    KECCAK_CHI5_NUM_VARIABLE_OFFSETS,
>;

struct Execution {
    column_parity:
        Vec<Row<KECCAK_COLUMN_PARITY_X11_NUM_WRITES, KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS>>,
    theta_rho: Vec<Row<KECCAK_THETA_RHO_X11_NUM_WRITES, KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS>>,
    chi5: Vec<Row<KECCAK_CHI5_X11_NUM_WRITES, KECCAK_CHI5_NUM_VARIABLE_OFFSETS>>,
}

fn retimed_execution(
    calls: &(ColumnParity, ThetaRho, Chi5),
    invocation: impl Fn(TimestampScalar) -> Option<i64>,
    read: impl Fn(TimestampScalar, TimestampScalar) -> i64,
) -> Execution {
    let (column_parity, theta_rho, chi5) = calls;
    Execution {
        column_parity: column_parity.retimed(|row| {
            invocation(row.write_timestamp)
                .map(|delta| retime(row, delta, |t| read(row.write_timestamp, t)))
        }),
        theta_rho: theta_rho.retimed(|row| {
            invocation(row.write_timestamp)
                .map(|delta| retime(row, delta, |t| read(row.write_timestamp, t)))
        }),
        chi5: chi5.retimed(|row| {
            invocation(row.write_timestamp)
                .map(|delta| retime(row, delta, |t| read(row.write_timestamp, t)))
        }),
    }
}

fn unmatched_reads(calls: &(ColumnParity, ThetaRho, Chi5), execution: &Execution) -> Tuples {
    let (column_parity, theta_rho, chi5) = calls;
    let (mut writes, _) = column_parity.tuples(&execution.column_parity);
    let (theta_rho_writes, theta_rho_reads) = theta_rho.tuples(&execution.theta_rho);
    let (chi5_writes, chi5_reads) = chi5.tuples(&execution.chi5);
    writes.extend(theta_rho_writes);
    writes.extend(chi5_writes);
    assert!(writes.iter().all(|(_, _, timestamp, _)| timestamp % 4 == 3));
    theta_rho_reads
        .union(&chi5_reads)
        .filter(|read| !writes.contains(read))
        .copied()
        .collect()
}

fn over_consumed(
    calls: &(ColumnParity, ThetaRho, Chi5),
    execution: &Execution,
    extra_reads: &[Tuple],
    extra_writes: &[Tuple],
) -> Vec<Tuple> {
    let (column_parity, theta_rho, chi5) = calls;
    let mut reads = BTreeMap::<Tuple, usize>::new();
    let mut writes = BTreeMap::<Tuple, usize>::new();
    for (circuit_writes, circuit_reads) in [
        column_parity.tuples(&execution.column_parity),
        theta_rho.tuples(&execution.theta_rho),
        chi5.tuples(&execution.chi5),
    ] {
        for tuple in circuit_writes {
            *writes.entry(tuple).or_default() += 1;
        }
        for tuple in circuit_reads {
            *reads.entry(tuple).or_default() += 1;
        }
    }
    for tuple in extra_writes {
        *writes.entry(*tuple).or_default() += 1;
    }
    for tuple in extra_reads {
        *reads.entry(*tuple).or_default() += 1;
    }
    reads
        .into_iter()
        .filter(|(tuple, count)| {
            tuple.2 % 4 == 3 && *count > writes.get(tuple).copied().unwrap_or(0)
        })
        .map(|(tuple, _)| tuple)
        .collect()
}

fn interleaved_touch_is_rejected(
    calls: &(ColumnParity, ThetaRho, Chi5),
    row: usize,
    lane: usize,
    store: bool,
) {
    let (_, _, chi5) = calls;
    let honest = retimed_execution(calls, |_| Some(0), |_, _| 0);
    let reader = chi5.rows[row];
    let base = reader.reg_accesses[1].read_value;
    let words: Vec<Tuple> = (0..2)
        .map(|half| {
            let access = reader.indirect_writes[2 * lane + half];
            (
                false,
                base + 8 * reader.variables_offsets[lane] as u32 + 4 * half as u32,
                access.timestamp.as_scalar(),
                access.read_value,
            )
        })
        .collect();
    let (_, chi5_reads) = chi5.tuples(&honest.chi5);
    assert!(words.iter().all(|word| chi5_reads.contains(word)));
    let touched: Vec<Tuple> = words
        .iter()
        .map(|&(is_register, address, timestamp, value)| {
            (
                is_register,
                address,
                timestamp + 1,
                if store { !value } else { value },
            )
        })
        .collect();
    assert!(touched
        .iter()
        .all(|(_, _, t, _)| *t < reader.write_timestamp));

    assert_eq!(over_consumed(calls, &honest, &words, &touched), words);

    let mut rows = chi5.rows.clone();
    let repointed_row = &mut rows[row];
    for (half, &(_, _, timestamp, value)) in touched.iter().enumerate() {
        let access = &mut repointed_row.indirect_writes[2 * lane + half];
        access.timestamp = TimestampData::from_scalar(timestamp);
        access.read_value = value;
    }
    let lanes: [u64; 5] = core::array::from_fn(|i| {
        repointed_row.indirect_writes[2 * i].read_value as u64
            | (repointed_row.indirect_writes[2 * i + 1].read_value as u64) << 32
    });
    for k in 0..5 {
        let chi = lanes[k] ^ (!lanes[(k + 1) % 5] & lanes[(k + 2) % 5]);
        repointed_row.indirect_writes[2 * k].write_value = chi as u32;
        repointed_row.indirect_writes[2 * k + 1].write_value = (chi >> 32) as u32;
    }
    if !store {
        let repointed = Execution {
            column_parity: honest.column_parity.clone(),
            theta_rho: honest.theta_rho.clone(),
            chi5: rows.clone(),
        };
        assert!(over_consumed(calls, &repointed, &words, &touched).is_empty());
    }
    let artifact = chi5.artifact(VARIANTS[0]);
    let constraints = lowered_constraints(&artifact);
    let group = artifact
        .aux_layout_data
        .relative_timestamp_groups
        .iter()
        .find(|group| {
            group
                .members
                .contains(&(NUM_KECCAK_F1600_REGISTER_ACCESSES + 2 * lane))
        })
        .unwrap();
    let trace = chi5.trace(&artifact, &rows);
    let [low, ..] = addresses(group);
    assert!(failing(&constraints, &trace, row)
        .iter()
        .any(|inputs| inputs.contains(&low)));
}

fn relations_hold<D: DelegationAbiDescription, const IW: usize, const VO: usize>(
    circuit: &KeccakCircuit<D, IW, VO>,
    rows: &[Row<IW, VO>],
) -> Vec<bool> {
    let artifact = circuit.artifact(VARIANTS[0]);
    let constraints = lowered_constraints(&artifact);
    let trace = circuit.trace(&artifact, rows);
    (0..rows.len())
        .map(|row| failing(&constraints, &trace, row).is_empty())
        .collect()
}

fn grouped_reads_in<const IW: usize, const VO: usize>(
    rows: &[Row<IW, VO>],
    reader: impl Fn(TimestampScalar) -> bool,
    producer: impl Fn(TimestampScalar) -> bool,
) -> usize {
    rows.iter()
        .filter(|row| reader(row.write_timestamp))
        .map(|row| read_timestamps(row).filter(|t| producer(*t)).count())
        .sum()
}

fn interleaved_cycle_is_rejected(calls: &(ColumnParity, ThetaRho, Chi5), gap: TimestampScalar) {
    let (_, theta_rho, chi5) = calls;
    let after = |invocation: TimestampScalar| invocation > gap;
    let forged = retimed_execution(
        calls,
        |i| Some(if after(i) { 4 } else { 0 }),
        |i, _| {
            if after(i) {
                4
            } else {
                0
            }
        },
    );
    assert!(relations_hold(theta_rho, &forged.theta_rho)
        .iter()
        .all(|ok| *ok));
    assert!(relations_hold(chi5, &forged.chi5).iter().all(|ok| *ok));
    let unmatched = unmatched_reads(calls, &forged);
    let expected = grouped_reads_in(&theta_rho.rows, after, |t| t <= gap)
        + grouped_reads_in(&chi5.rows, after, |t| t <= gap);
    assert!(expected > 0);
    assert_eq!(unmatched.len(), expected, "gap {gap}");
    assert!(unmatched.iter().all(|(_, _, t, _)| t - 4 <= gap));

    let honest = retimed_execution(
        calls,
        |i| Some(if after(i) { 4 } else { 0 }),
        |i, t| {
            if after(i) && t > gap {
                4
            } else {
                0
            }
        },
    );
    assert!(unmatched_reads(calls, &honest).is_empty());
    for (rows, held) in [
        (
            theta_rho
                .rows
                .iter()
                .map(|row| {
                    (
                        row.write_timestamp,
                        read_timestamps(row).collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
            relations_hold(theta_rho, &honest.theta_rho),
        ),
        (
            chi5.rows
                .iter()
                .map(|row| {
                    (
                        row.write_timestamp,
                        read_timestamps(row).collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
            relations_hold(chi5, &honest.chi5),
        ),
    ] {
        for ((invocation, reads), held) in rows.iter().zip(held) {
            let off_schedule = after(*invocation) && reads.iter().any(|t| *t <= gap);
            assert_eq!(held, !off_schedule, "gap {gap} invocation {invocation}");
        }
    }
}

fn interior_entry_is_rejected(calls: &(ColumnParity, ThetaRho, Chi5), entry: usize) {
    let (column_parity, theta_rho, chi5) = calls;
    let start = column_parity.rows[0].write_timestamp;
    let skip = (4 * entry) as TimestampScalar;
    let end = start + 4 * NUM_KECCAK_F1600_CALLS as TimestampScalar;
    let shifted = |invocation: TimestampScalar| invocation >= start + skip && invocation < end;
    let forged = retimed_execution(
        calls,
        |i| match i {
            i if i >= start && i < start + skip => None,
            i if shifted(i) => Some(-(skip as i64)),
            _ => Some(0),
        },
        |i, _| if shifted(i) { -(skip as i64) } else { 0 },
    );
    assert!(relations_hold(theta_rho, &forged.theta_rho)
        .iter()
        .all(|ok| *ok));
    assert!(relations_hold(chi5, &forged.chi5).iter().all(|ok| *ok));
    let unmatched = unmatched_reads(calls, &forged);
    let skipped = |t: TimestampScalar| t >= start && t < start + skip;
    let expected = grouped_reads_in(&theta_rho.rows, shifted, skipped)
        + grouped_reads_in(&chi5.rows, shifted, skipped);
    assert!(expected > 0);
    assert_eq!(unmatched.len(), expected, "entry {entry}");
    assert!(unmatched.iter().all(|(_, _, t, _)| *t < start));
}

#[test]
fn theta_rho_relative_timestamps_reach_the_compiled_relations() {
    tampering_reaches_the_relations(&theta_rho(&keccak_vm()));
}

#[test]
fn chi5_relative_timestamps_reach_the_compiled_relations() {
    tampering_reaches_the_relations(&chi5(&keccak_vm()));
}

#[test]
fn relative_timestamp_borrows_follow_the_limb_boundaries() {
    let vm = keccak_vm();
    let theta_rho_distances = borrows_follow_the_limb_boundaries(&theta_rho(&vm));
    assert_eq!(theta_rho_distances, BTreeSet::from([4, 8, 12, 16, 20, 24]));
    let chi5_distances = borrows_follow_the_limb_boundaries(&chi5(&vm));
    assert_eq!(
        chi5_distances,
        (1..=9).map(|calls| 4 * calls).collect::<BTreeSet<_>>()
    );
}

#[test]
fn relative_timestamp_group_members_must_agree() {
    let vm = keccak_vm();
    disagreeing_members_are_refused(&theta_rho(&vm));
    disagreeing_members_are_refused(&chi5(&vm));
}

#[test]
fn relative_timestamps_bind_reads_to_their_scheduled_producers() {
    let vm = keccak_vm();
    let counters = vm.counters;
    assert_eq!(
        [
            counters.blake_calls,
            counters.bigint_calls,
            counters.keccak_calls,
            counters.blake_g_function_calls
        ],
        [0; 4]
    );
    let calls = (column_parity(&vm), theta_rho(&vm), chi5(&vm));
    assert!(over_consumed(
        &calls,
        &retimed_execution(&calls, |_| Some(0), |_, _| 0),
        &[],
        &[]
    )
    .is_empty());
    let (_, theta_rho, chi5) = &calls;
    interleaved_cycle_is_rejected(&calls, theta_rho.rows[15].write_timestamp - 1);
    interleaved_cycle_is_rejected(&calls, chi5.rows[37].write_timestamp - 1);
    interior_entry_is_rejected(&calls, 1);
    interior_entry_is_rejected(&calls, 5);
    interior_entry_is_rejected(&calls, 10);
    interleaved_touch_is_rejected(&calls, 42, 2, false);
    interleaved_touch_is_rejected(&calls, 42, 2, true);
}
