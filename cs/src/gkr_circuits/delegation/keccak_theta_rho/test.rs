use super::*;
use crate::cs::circuit_impl::BasicAssembly;
use crate::cs::circuit_output::CircuitOutput;
use crate::oracle::*;
use crate::structured_expr::StructuredStatement;
use crate::tables::{IndexLookupFn, LookupWrapper};
use crate::witness_placer::cs_debug_evaluator::CSDebugWitnessEvaluator;
use ::field::baby_bear::base::BabyBearField;
use std::sync::OnceLock;

pub(crate) fn pi(round: usize, i: usize) -> usize {
    KECCAK_F1600_PERMUTATIONS[round][i]
}

pub(crate) fn schedule_step(state: &mut [u64; 31], control: u32) -> u32 {
    let (precompile, x, round) = keccak_f1600_decode_control(control);
    let theta_rho = |state: &mut [u64; 31], d: u64| {
        for y in 0..5 {
            let slot = pi(round, x + 5 * y);
            state[slot] = (state[slot] ^ d).rotate_left(KECCAK_F1600_RHO[x][y]);
        }
    };
    match precompile {
        KECCAK_COLUMN_PARITY_PRECOMPILE => {
            let slot = |y: usize| pi(round, x + 5 * y);
            if x == 0 {
                state[slot(0)] ^= KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED[round];
            }
            state[25 + x] = (0..5).fold(0, |acc, y| acc ^ state[slot(y)]);
        }
        KECCAK_THETA_RHO_PRECOMPILE => {
            let d = state[25 + (x + 4) % 5] ^ state[25 + (x + 1) % 5].rotate_left(1);
            theta_rho(state, d);
        }
        KECCAK_CHI5_PRECOMPILE => {
            let slots: [usize; 5] = from_fn(|k| pi(round + 1, 5 * x + k));
            let a = slots.map(|slot| state[slot]);
            for k in 0..5 {
                state[slots[k]] = a[k] ^ (!a[(k + 1) % 5] & a[(k + 2) % 5]);
            }
        }
        _ => unreachable!("{control:#x}"),
    }
    keccak_f1600_bump_control(control)
}

fn keccak_f_reference(a: &mut [u64; 25]) {
    for round in 0..24 {
        let c: [u64; 5] = from_fn(|x| (0..5).fold(0, |acc, y| acc ^ a[x + 5 * y]));
        let mut b = [0u64; 25];
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] =
                    (a[x + 5 * y] ^ d).rotate_left(KECCAK_F1600_RHO[x][y]);
            }
        }
        for y in 0..5 {
            for x in 0..5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
            }
        }
        a[0] ^= KECCAK_F1600_ROUND_CONSTANTS_ADJUSTED[round + 1];
    }
}

pub(crate) fn pseudo_random_state(seed: u64) -> [u64; 25] {
    let mut v = seed ^ 0x9E3779B97F4A7C15;
    from_fn(|_| {
        v ^= v << 13;
        v ^= v >> 7;
        v ^= v << 17;
        v
    })
}

// every call of one permutation: (control in, state before)
pub(crate) fn schedule_trace(lanes: [u64; 25]) -> (Vec<(u32, [u64; 31])>, [u64; 31]) {
    let mut state = [0u64; 31];
    state[..25].copy_from_slice(&lanes);
    let mut control = 0;
    let mut calls = Vec::new();
    for _ in 0..NUM_KECCAK_F1600_CALLS {
        calls.push((control, state));
        control = schedule_step(&mut state, control);
    }
    (calls, state)
}

#[test]
fn schedule_computes_keccak_f() {
    let (_, state) = schedule_trace([0; 25]);
    assert_eq!(state[0], 0xF1258F7940E1DDE7);
    assert_eq!(state[1], 0x84D5CCF933C0478A);
    for seed in 1..4 {
        let lanes = pseudo_random_state(seed);
        let mut expected = lanes;
        keccak_f_reference(&mut expected);
        assert_eq!(schedule_trace(lanes).1[..25], expected);
    }
}

// variable offset i addresses slot indices[i], two u32 words per slot
#[derive(Clone, Copy)]
pub(crate) struct KeccakRowOracle {
    pub(crate) csr: u32,
    pub(crate) execute: bool,
    pub(crate) control_in: u32,
    pub(crate) control_out: u32,
    pub(crate) indices: [usize; 7],
    pub(crate) state_in: [u64; 31],
    pub(crate) state_out: [u64; 31],
}

impl KeccakRowOracle {
    pub(crate) fn padding(csr: u32) -> Self {
        Self {
            csr,
            execute: false,
            control_in: 0,
            control_out: 0,
            indices: [0; 7],
            state_in: [0; 31],
            state_out: [0; 31],
        }
    }

    // a padding row whose x10 is this row's control key, so the lookups select this row
    pub(crate) fn padding_with_key_of(row: Self) -> Self {
        Self {
            control_in: row.control_in | KECCAK_F1600_CONTROL_EXECUTE_FLAG,
            control_out: row.control_out,
            indices: row.indices,
            ..Self::padding(row.csr)
        }
    }
}

fn word(state: &[u64; 31], slot: usize, half: usize) -> u32 {
    (state[slot] >> (32 * half)) as u32
}

impl<F: PrimeField> Oracle<F> for KeccakRowOracle {
    fn get_witness_from_placeholder(&self, placeholder: Placeholder, _: usize, _: usize) -> F {
        panic!("unsupported field placeholder {placeholder:?}")
    }

    fn get_u32_witness_from_placeholder(&self, placeholder: Placeholder, _: usize) -> u32 {
        match placeholder {
            Placeholder::DelegationRegisterReadValue(10) => self.control_in,
            Placeholder::DelegationRegisterWriteValue(10) => self.control_out,
            Placeholder::DelegationRegisterReadValue(11) => 0x1000,
            Placeholder::DelegationIndirectReadValue {
                register_index: 11,
                word_index,
            } => word(&self.state_in, self.indices[word_index / 2], word_index % 2),
            Placeholder::DelegationIndirectWriteValue {
                register_index: 11,
                word_index,
            } => word(
                &self.state_out,
                self.indices[word_index / 2],
                word_index % 2,
            ),
            a => panic!("unsupported u32 placeholder {a:?}"),
        }
    }

    fn get_u16_witness_from_placeholder(&self, placeholder: Placeholder, _: usize) -> u16 {
        match placeholder {
            Placeholder::DelegationABIOffset => 0,
            Placeholder::DelegationType => self.csr as u16,
            Placeholder::DelegationIndirectAccessVariableOffset { variable_index } => {
                self.indices[variable_index] as u16
            }
            a => panic!("unsupported u16 placeholder {a:?}"),
        }
    }

    fn get_boolean_witness_from_placeholder(&self, placeholder: Placeholder, _: usize) -> bool {
        match placeholder {
            Placeholder::ExecuteDelegation => self.execute,
            a => panic!("unsupported boolean placeholder {a:?}"),
        }
    }

    fn get_timestamp_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        _: usize,
    ) -> TimestampScalar {
        if !self.execute {
            return 0;
        }
        match placeholder {
            Placeholder::DelegationWriteTimestamp => 1 << 10,
            Placeholder::DelegationRegisterReadTimestamp(_) => 1 << 9,
            Placeholder::DelegationIndirectReadTimestamp { .. } => 1 << 8,
            a => panic!("unsupported timestamp placeholder {a:?}"),
        }
    }

    fn get_executor_family_data(&self, _: usize) -> crate::gkr_circuits::ExecutorFamilyDecoderData {
        unreachable!()
    }
}

pub(crate) type DebugAssembly =
    BasicAssembly<BabyBearField, CSDebugWitnessEvaluator<BabyBearField>, false>;

pub(crate) type Tables = Vec<(TableType, LookupWrapper<BabyBearField>)>;

// lookups must check the whole tuple: the fast index functions only look at keys
pub(crate) fn generated_tables<const W: usize>(table_types: Vec<TableType>) -> Tables {
    table_types
        .into_iter()
        .map(|table_type| {
            let mut table = table_type.generate_table::<BabyBearField, W>();
            if let LookupWrapper::Initialized(inner) = &mut table {
                inner.quick_index_lookup_fn = IndexLookupFn::None;
            }
            (table_type, table)
        })
        .collect()
}

pub(crate) fn satisfied(
    oracle: KeccakRowOracle,
    tables: &Tables,
    define: fn(&mut DebugAssembly),
) -> bool {
    let mut cs = DebugAssembly::new_with_oracle(oracle);
    for (table_type, table) in tables {
        cs.add_table_with_content(*table_type, table.clone());
    }
    define(&mut cs);
    cs.is_satisfied()
}

// the untampered row must pass, so a rejection cannot come from a broken harness
pub(crate) fn rejected(
    honest: KeccakRowOracle,
    tampered: KeccakRowOracle,
    tables: &Tables,
    define: fn(&mut DebugAssembly),
) -> bool {
    assert!(satisfied(honest, tables, define));
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        satisfied(tampered, tables, define)
    }))
    .map_or(true, |ok| !ok)
}

#[derive(Debug, PartialEq)]
enum Violation {
    Constraint,
    Boolean,
    Lookup(TableType),
}

fn table(tables: &Tables, table_type: TableType) -> &LookupWrapper<BabyBearField> {
    &tables.iter().find(|(t, _)| *t == table_type).unwrap().1
}

fn violations(
    output: &CircuitOutput<BabyBearField>,
    placer: &mut CSDebugWitnessEvaluator<BabyBearField>,
) -> Vec<Violation> {
    let mut violations = vec![];
    for statement in output.structured_statements.iter() {
        let satisfied = match statement {
            StructuredStatement::AssertZero {
                compiled_constraint,
                ..
            } => {
                compiled_constraint.evaluate_with_placer(placer)
                    == <BabyBearField as ::field::Field>::ZERO
            }
            StructuredStatement::Define { .. } => unreachable!(),
        };
        if !satisfied {
            violations.push(Violation::Constraint);
        }
    }
    for &variable in output.boolean_vars.iter() {
        let mut square = placer.get_field(variable);
        square.mul_assign(&placer.get_field(variable));
        if square != placer.get_field(variable) {
            violations.push(Violation::Boolean);
        }
    }
    for query in output.lookups.iter() {
        let LookupQueryTableType::Constant(table_type) = query.table else {
            unreachable!()
        };
        let row: Vec<_> = query
            .row
            .iter()
            .map(|input| input.evaluate(placer))
            .collect();
        let table = table(tables(), table_type);
        if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| table.lookup_row(&row)))
            .is_err()
        {
            violations.push(Violation::Lookup(table_type));
        }
    }
    violations
}

fn tampered_violations(
    oracle: KeccakRowOracle,
    tamper: impl FnOnce(&CircuitOutput<BabyBearField>, &mut CSDebugWitnessEvaluator<BabyBearField>),
) -> Vec<Violation> {
    let mut cs = DebugAssembly::new_with_oracle(oracle);
    for (table_type, table) in tables() {
        cs.add_table_with_content(*table_type, table.clone());
    }
    define_keccak_theta_rho_delegation_circuit(&mut cs);
    let (output, placer) = cs.finalize();
    let mut placer = placer.unwrap();
    assert_eq!(violations(&output, &mut placer), vec![]);
    tamper(&output, &mut placer);
    violations(&output, &mut placer)
}

pub(crate) fn schedule_rows(
    precompile: u32,
    seed: u64,
    indices: impl Fn(usize, usize) -> Vec<usize>,
) -> Vec<KeccakRowOracle> {
    schedule_trace(pseudo_random_state(seed))
        .0
        .into_iter()
        .filter(|&(control, _)| keccak_f1600_decode_control(control).0 == precompile)
        .map(|(control_in, state_in)| {
            let (_, x, round) = keccak_f1600_decode_control(control_in);
            let mut state_out = state_in;
            let control_out = schedule_step(&mut state_out, control_in);
            let slots = indices(x, round);
            KeccakRowOracle {
                csr: keccak_f1600_csr_for_precompile(precompile),
                execute: true,
                control_in,
                control_out,
                indices: from_fn(|i| slots.get(i).copied().unwrap_or(0)),
                state_in,
                state_out,
            }
        })
        .collect()
}

fn byte_d_variables(output: &CircuitOutput<BabyBearField>) -> [Vec<Variable>; 3] {
    let rows: Vec<_> = output
        .lookups
        .iter()
        .filter(|query| query.table == LookupQueryTableType::Constant(TableType::Xor))
        .map(|query| &query.row)
        .collect();
    let rotated_terms = |row: &Vec<LookupInput<BabyBearField>>| match &row[1] {
        LookupInput::Expression { linear_terms, .. } => linear_terms.clone(),
        LookupInput::Variable(variable) => {
            vec![(<BabyBearField as ::field::Field>::ONE, *variable)]
        }
    };
    let mut minus_256 = BabyBearField::from_u32_unchecked(256);
    ::field::Field::negate(&mut minus_256);
    let top = rows
        .iter()
        .skip(1)
        .step_by(2)
        .map(|row| {
            let terms = rotated_terms(row);
            let [(_, variable)] = terms
                .iter()
                .filter(|(coeff, _)| *coeff == minus_256)
                .collect::<Vec<_>>()[..]
            else {
                unreachable!()
            };
            *variable
        })
        .collect();
    let rotated_low = rows
        .iter()
        .step_by(2)
        .map(|row| match rotated_terms(row)[..] {
            [(_, variable)] => variable,
            _ => unreachable!(),
        })
        .collect();
    let d = rows
        .iter()
        .map(|row| match row[2] {
            LookupInput::Variable(variable) => variable,
            _ => unreachable!(),
        })
        .collect();
    [top, rotated_low, d]
}

fn rederive_lanes_from_d(
    output: &CircuitOutput<BabyBearField>,
    placer: &mut CSDebugWitnessEvaluator<BabyBearField>,
) {
    for query in output.lookups.iter() {
        if query.table != LookupQueryTableType::Constant(TableType::KeccakXorSplit) {
            continue;
        }
        let keys: Vec<_> = query.row[..3]
            .iter()
            .map(|input| input.evaluate(placer))
            .collect();
        let (_, fragments) =
            table(tables(), TableType::KeccakXorSplit).lookup_values_and_get_index::<2>(&keys);
        for (input, fragment) in query.row[3..].iter().zip(fragments) {
            let LookupInput::Variable(variable) = input else {
                unreachable!()
            };
            placer.values[variable.0 as usize] = fragment;
        }
    }
    for statement in output.structured_statements.iter() {
        let StructuredStatement::AssertZero {
            compiled_constraint,
            ..
        } = statement
        else {
            continue;
        };
        let (_, linear, _) = compiled_constraint.clone().split_max_quadratic();
        let [(coeff, variable)] = linear[..] else {
            continue;
        };
        let mut residual = compiled_constraint.evaluate_with_placer(placer);
        if residual == <BabyBearField as ::field::Field>::ZERO {
            continue;
        }
        residual.mul_assign(&::field::Field::inverse(&coeff).unwrap());
        placer.values[variable.0 as usize].sub_assign(&residual);
    }
}

fn theta_rho_indices(x: usize, round: usize) -> Vec<usize> {
    (0..5)
        .map(|y| pi(round, x + 5 * y))
        .chain([25 + (x + 4) % 5, 25 + (x + 1) % 5])
        .collect()
}

fn rows(seed: u64) -> Vec<KeccakRowOracle> {
    schedule_rows(KECCAK_THETA_RHO_PRECOMPILE, seed, theta_rho_indices)
}

fn tables() -> &'static Tables {
    static TABLES: OnceLock<Tables> = OnceLock::new();
    TABLES.get_or_init(|| generated_tables::<TOTAL_TABLE_WIDTH>(all_table_types()))
}

fn satisfied_row(oracle: KeccakRowOracle) -> bool {
    satisfied(oracle, tables(), define_keccak_theta_rho_delegation_circuit)
}

fn rejected_row(honest: KeccakRowOracle, tampered: KeccakRowOracle) -> bool {
    rejected(
        honest,
        tampered,
        tables(),
        define_keccak_theta_rho_delegation_circuit,
    )
}

// outputs consistent with the slots actually read
fn recompute(oracle: &mut KeccakRowOracle) {
    let (_, x, _) = keccak_f1600_decode_control(oracle.control_in);
    let s = oracle.state_in;
    let d = s[oracle.indices[5]] ^ s[oracle.indices[6]].rotate_left(1);
    oracle.state_out = s;
    for y in 0..5 {
        let slot = oracle.indices[y];
        oracle.state_out[slot] = (s[slot] ^ d).rotate_left(KECCAK_F1600_RHO[x][y]);
    }
}

#[test]
fn theta_rho_rows_are_satisfied() {
    let rows = rows(1);
    assert_eq!(rows.len(), NUM_KECCAK_F1600_THETA_RHO_CALLS);
    for oracle in rows {
        assert!(satisfied_row(oracle), "control {:#x}", oracle.control_in);
    }
    assert!(satisfied_row(KeccakRowOracle::padding(
        KECCAK_THETA_RHO_CSR_REGISTER
    )));
}

#[test]
fn theta_rho_rejections() {
    let rows = rows(2);
    // every written u16 limb, at a bit that varies with the lane, limb and row
    for y in 0..5 {
        for m in 0..4 {
            let call = (29 * (4 * y + m) + 7) % rows.len();
            let bit = 16 * m + (5 * y + 3 * m + call) % 16;
            let mut oracle = rows[call];
            oracle.state_out[oracle.indices[y]] ^= 1 << bit;
            assert!(
                rejected_row(rows[call], oracle),
                "call {call} lane {y} bit {bit}"
            );
        }
    }
    // the C slots are read only: a written value there is not part of the row, the read value is
    for (call, position, bit) in [(8, 5, 3), (44, 6, 50)] {
        let mut oracle = rows[call];
        oracle.state_out[oracle.indices[position]] ^= 1 << bit;
        assert!(satisfied_row(oracle), "call {call} slot {position}");
        let mut oracle = rows[call];
        oracle.state_in[oracle.indices[position]] ^= 1 << bit;
        assert!(
            rejected_row(rows[call], oracle),
            "call {call} slot {position}"
        );
    }
    for (call, delta) in [(2, 1u32 << 6), (4, 1 << 3), (9, 1)] {
        let mut oracle = rows[call];
        oracle.control_out += delta;
        assert!(
            rejected_row(rows[call], oracle),
            "call {call} delta {delta}"
        );
    }
    {
        let mut oracle = rows[12];
        let (_, x, _) = keccak_f1600_decode_control(oracle.control_in);
        let slot = oracle.indices[3];
        let unrotated = oracle.state_out[slot].rotate_right(KECCAK_F1600_RHO[x][3]);
        oracle.state_out[slot] = unrotated.rotate_left(KECCAK_F1600_RHO[(x + 1) % 5][3]);
        assert!(rejected_row(rows[12], oracle));
    }
    for (call, position) in [(6, 0), (17, 3), (21, 5), (21, 6)] {
        let mut oracle = rows[call];
        oracle.indices[position] = if position < 5 {
            (0..25).find(|slot| !oracle.indices.contains(slot)).unwrap()
        } else {
            (25..31)
                .find(|slot| !oracle.indices.contains(slot))
                .unwrap()
        };
        recompute(&mut oracle);
        assert!(
            rejected_row(rows[call], oracle),
            "call {call} position {position}"
        );
    }
    let mut oracle = rows[3];
    oracle.control_in = oracle.control_in - KECCAK_THETA_RHO_PRECOMPILE + 4;
    assert!(rejected_row(rows[3], oracle));
    let padding = KeccakRowOracle::padding(KECCAK_THETA_RHO_CSR_REGISTER);
    assert!(rejected_row(
        padding,
        KeccakRowOracle::padding_with_key_of(rows[3])
    ));
}

#[test]
fn theta_rho_byte_d_rejections() {
    let rows = rows(3);
    let tampered = |call: usize,
                    tamper: &dyn Fn(
        &CircuitOutput<BabyBearField>,
        &[Vec<Variable>; 3],
        &mut CSDebugWitnessEvaluator<BabyBearField>,
    )| {
        tampered_violations(rows[call], |output, placer| {
            let variables = byte_d_variables(output);
            assert_eq!(variables.each_ref().map(Vec::len), [4, 4, 8]);
            tamper(output, &variables, placer)
        })
    };
    let assign =
        |placer: &mut CSDebugWitnessEvaluator<BabyBearField>, variable: Variable, value: u64| {
            placer.values[variable.0 as usize] = BabyBearField::from_u32_unchecked(value as u32);
        };
    let mut lift = ::field::Field::inverse(&BabyBearField::from_u32_unchecked(1 << 16)).unwrap();
    ::field::Field::negate(&mut lift);
    let mut top_bits_seen = [false; 2];
    let mut lifted = 0;
    for call in [0, 13, 57, 119] {
        let c_prev = rows[call].state_in[rows[call].indices[5]];
        let rotated = rows[call].state_in[rows[call].indices[6]].rotate_left(1);
        for m in 0..4 {
            top_bits_seen[(rotated >> (16 * ((m + 1) % 4))) as usize & 1] = true;
            let violations = tampered(call, &|_, [top, ..], placer| {
                let bit = &mut placer.values[top[m].0 as usize];
                *bit = BabyBearField::from_u32_unchecked(1 - bit.as_u32_reduced());
            });
            assert!(
                !violations.is_empty()
                    && violations
                        .iter()
                        .all(|v| *v == Violation::Lookup(TableType::Xor)),
                "call {call} top bit {m}: {violations:?}"
            );
            let next = (m + 1) % 4;
            let limb = |k: usize| (rotated >> (16 * k)) & 0xffff;
            if limb(m) == 0xffff || limb(next) + lift.as_u32_reduced() as u64 > 0xffff {
                continue;
            }
            lifted += 1;
            let lifted_rotated =
                rotated + (1 << (16 * m)) + ((lift.as_u32_reduced() as u64) << (16 * next));
            let violations = tampered(call, &|output, [top, rotated_low, d], placer| {
                placer.values[top[m].0 as usize].add_assign(&lift);
                for k in 0..4 {
                    assign(placer, rotated_low[k], (lifted_rotated >> (16 * k)) & 0xff);
                }
                for j in 0..8 {
                    assign(placer, d[j], ((c_prev ^ lifted_rotated) >> (8 * j)) & 0xff);
                }
                rederive_lanes_from_d(output, placer);
            });
            assert_eq!(
                violations,
                vec![Violation::Boolean],
                "call {call} top bit {m}"
            );
        }
        for j in 0..8 {
            let violations = tampered(call, &|output, [_, _, d], placer| {
                let byte = placer.values[d[j].0 as usize].as_u32_reduced() as u64;
                assign(placer, d[j], byte ^ (1 << j));
                rederive_lanes_from_d(output, placer);
            });
            assert_eq!(
                violations,
                vec![Violation::Lookup(TableType::Xor)],
                "call {call} D byte {j}"
            );
        }
    }
    assert_eq!(top_bits_seen, [true; 2]);
    assert!(lifted > 0);
}
