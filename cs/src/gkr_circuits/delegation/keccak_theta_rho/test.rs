use super::*;
use crate::cs::circuit_impl::BasicAssembly;
use crate::oracle::*;
use crate::tables::{IndexLookupFn, LookupWrapper, KECCAK_PERMUTATIONS_ADJUSTED};
use crate::witness_placer::cs_debug_evaluator::CSDebugWitnessEvaluator;
use ::field::baby_bear::base::BabyBearField;
use common_constants::delegation_types::keccak_k2::{
    KECCAK_CHI5_PRECOMPILE, KECCAK_THETA_RHO_PRECOMPILE, NUM_DELEGATION_CALLS_FOR_KECCAK_K2_F1600,
};
use std::sync::OnceLock;

pub(crate) const ROUND_CONSTANTS_ADJUSTED: [u64; 25] = [
    0,
    1,
    32898,
    9223372036854808714,
    9223372039002292224,
    32907,
    2147483649,
    9223372039002292353,
    9223372036854808585,
    138,
    136,
    2147516425,
    2147483658,
    2147516555,
    9223372036854775947,
    9223372036854808713,
    9223372036854808579,
    9223372036854808578,
    9223372036854775936,
    32778,
    9223372039002259466,
    9223372039002292353,
    9223372036854808704,
    2147483649,
    9223372039002292232,
];

pub(crate) fn pi(round: usize, i: usize) -> usize {
    KECCAK_PERMUTATIONS_ADJUSTED[round * 25 + i] as usize
}

pub(crate) fn decode(control: u32) -> (u32, usize, usize) {
    (
        control & 7,
        (control >> 3 & 7) as usize,
        (control >> 6) as usize,
    )
}

pub(crate) fn encode(precompile: u32, iteration: usize, round: usize) -> u32 {
    precompile | (iteration as u32) << 3 | (round as u32) << 6
}

pub(crate) fn schedule_step(state: &mut [u64; 31], control: u32) -> u32 {
    let (precompile, x, round) = decode(control);
    let next_in_loop = |next: u32| {
        if x == 4 {
            encode(next, 0, round)
        } else {
            encode(precompile, x + 1, round)
        }
    };
    let theta_rho = |state: &mut [u64; 31], d: u64| {
        for y in 0..5 {
            let slot = pi(round, x + 5 * y);
            state[slot] = (state[slot] ^ d).rotate_left(KECCAK_RHO_OFFSETS[x][y]);
        }
    };
    match precompile {
        0 => {
            let slot = |y: usize| pi(round, x + 5 * y);
            if x == 0 {
                state[slot(0)] ^= ROUND_CONSTANTS_ADJUSTED[round];
            }
            state[25 + x] = (0..5).fold(0, |acc, y| acc ^ state[slot(y)]);
            next_in_loop(KECCAK_THETA_RHO_PRECOMPILE)
        }
        KECCAK_THETA_RHO_PRECOMPILE => {
            let d = state[25 + (x + 4) % 5] ^ state[25 + (x + 1) % 5].rotate_left(1);
            theta_rho(state, d);
            next_in_loop(KECCAK_CHI5_PRECOMPILE)
        }
        KECCAK_CHI5_PRECOMPILE => {
            let slots: [usize; 5] = from_fn(|k| pi(round + 1, 5 * x + k));
            let a = slots.map(|slot| state[slot]);
            for k in 0..5 {
                state[slots[k]] = a[k] ^ (!a[(k + 1) % 5] & a[(k + 2) % 5]);
            }
            if x == 4 {
                encode(0, 0, round + 1)
            } else {
                encode(KECCAK_CHI5_PRECOMPILE, x + 1, round)
            }
        }
        _ => unreachable!("{control:#x}"),
    }
}

fn keccak_f_reference(a: &mut [u64; 25]) {
    for round in 0..24 {
        let c: [u64; 5] = from_fn(|x| (0..5).fold(0, |acc, y| acc ^ a[x + 5 * y]));
        let mut b = [0u64; 25];
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] =
                    (a[x + 5 * y] ^ d).rotate_left(KECCAK_RHO_OFFSETS[x][y]);
            }
        }
        for y in 0..5 {
            for x in 0..5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
            }
        }
        a[0] ^= ROUND_CONSTANTS_ADJUSTED[round + 1];
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

// every call of one permutation: (control in, slots before)
pub(crate) fn schedule_trace(lanes: [u64; 25]) -> (Vec<(u32, [u64; 31])>, [u64; 31]) {
    let mut state = [0u64; 31];
    state[..25].copy_from_slice(&lanes);
    let mut control = 0;
    let mut calls = Vec::new();
    for _ in 0..NUM_DELEGATION_CALLS_FOR_KECCAK_K2_F1600 {
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
}

fn word(state: &[u64; 31], slot: usize, half: usize) -> u32 {
    (state[slot] >> (32 * half)) as u32
}

impl<F: PrimeField> Oracle<F> for KeccakRowOracle {
    fn get_witness_from_placeholder(&self, placeholder: Placeholder, _: usize, _: usize) -> F {
        panic!("unsupported field placeholder {placeholder:?}")
    }

    fn get_u32_witness_from_placeholder(&self, placeholder: Placeholder, _: usize) -> u32 {
        if !self.execute {
            return 0;
        }
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
                if self.execute {
                    self.indices[variable_index] as u16
                } else {
                    0
                }
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
pub(crate) fn full_membership(mut tables: Tables) -> Tables {
    for (_, table) in &mut tables {
        if let LookupWrapper::Initialized(inner) = table {
            inner.quick_index_lookup_fn = IndexLookupFn::None;
        }
    }
    tables
}

pub(crate) fn generated_tables<const W: usize>(table_types: Vec<TableType>) -> Tables {
    full_membership(
        table_types
            .into_iter()
            .map(|table_type| (table_type, table_type.generate_table::<BabyBearField, W>()))
            .collect(),
    )
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

pub(crate) fn schedule_rows(
    precompile: u32,
    seed: u64,
    csr: u32,
    indices: impl Fn(usize, usize) -> Vec<usize>,
) -> Vec<KeccakRowOracle> {
    schedule_trace(pseudo_random_state(seed))
        .0
        .into_iter()
        .filter(|&(control, _)| decode(control).0 == precompile)
        .map(|(control_in, state_in)| {
            let (_, x, round) = decode(control_in);
            let mut state_out = state_in;
            let control_out = schedule_step(&mut state_out, control_in);
            let slots = indices(x, round);
            KeccakRowOracle {
                csr,
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

fn theta_rho_indices(x: usize, round: usize) -> Vec<usize> {
    (0..5)
        .map(|y| pi(round, x + 5 * y))
        .chain([25 + (x + 4) % 5, 25 + (x + 1) % 5])
        .collect()
}

fn rows(seed: u64) -> Vec<KeccakRowOracle> {
    schedule_rows(
        KECCAK_THETA_RHO_PRECOMPILE,
        seed,
        KECCAK_THETA_RHO_CSR_REGISTER,
        theta_rho_indices,
    )
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
    let (_, x, _) = decode(oracle.control_in);
    let s = oracle.state_in;
    let d = s[oracle.indices[5]] ^ s[oracle.indices[6]].rotate_left(1);
    oracle.state_out = s;
    for y in 0..5 {
        let slot = oracle.indices[y];
        oracle.state_out[slot] = (s[slot] ^ d).rotate_left(KECCAK_RHO_OFFSETS[x][y]);
    }
}

#[test]
fn theta_rho_rows_are_satisfied() {
    let rows = rows(1);
    assert_eq!(rows.len(), 24 * 5);
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
    // the C lanes are written back unchanged
    for (call, position, bit) in [(8, 5, 3), (44, 6, 50)] {
        let mut oracle = rows[call];
        oracle.state_out[oracle.indices[position]] ^= 1 << bit;
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
        let (_, x, _) = decode(oracle.control_in);
        let slot = oracle.indices[3];
        let unrotated = oracle.state_out[slot].rotate_right(KECCAK_RHO_OFFSETS[x][3]);
        oracle.state_out[slot] = unrotated.rotate_left(KECCAK_RHO_OFFSETS[(x + 1) % 5][3]);
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
}
