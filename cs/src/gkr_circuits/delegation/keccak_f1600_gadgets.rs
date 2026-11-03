// Gadgets shared by the three Keccak-f1600 delegation circuits: x10 carries the control word, x11
// points at keccak_special5's 31-slot state, and each lane access is read-write or read-only.

use super::*;
use crate::cs::circuit::*;
use crate::definitions::*;
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::witness_placer::*;
use common_constants::delegation_types::keccak_f1600::{
    KECCAK_F1600_BASE_ABI_REGISTER, KECCAK_F1600_CONTROL_EXECUTE_FLAG,
};
use core::array::from_fn;

const CONTROL_REGISTER: usize = KECCAK_F1600_BASE_ABI_REGISTER as usize;
const STATE_REGISTER: usize = CONTROL_REGISTER + 1;

// low byte committed, high byte affine; callers must range-check both
pub(crate) fn split_bytes<F: PrimeField, CS: Circuit<F>, const N: usize>(
    cs: &mut CS,
    limbs: [Variable; N],
) -> [[Expr<F>; 2]; N] {
    let low: [Variable; N] = from_fn(|_| cs.add_variable());
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        let mask = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0xff);
        for m in 0..N {
            let limb = placer.get_u16(limbs[m]);
            placer.assign_u16(low[m], &limb.and(&mask));
        }
    });
    let inv256 = F::from_u32_unchecked(256).inverse().unwrap();
    from_fn(|m| {
        [
            Expr::var(low[m]),
            (Expr::var(limbs[m]) - Expr::var(low[m])) * Expr::constant(inv256),
        ]
    })
}

// three nibbles committed, the fourth affine; callers must range-check all four
pub(crate) fn split_nibbles<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    limbs: [Variable; 4],
) -> [Expr<F>; 16] {
    let digits: [[Variable; 3]; 4] = from_fn(|_| from_fn(|_| cs.add_variable()));
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        let mask = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(15);
        for m in 0..4 {
            let limb = placer.get_u16(limbs[m]);
            for j in 0..3 {
                placer.assign_u16(digits[m][j], &limb.shr(4 * j as u32).and(&mask));
            }
        }
    });
    let inv4096 = F::from_u32_unchecked(4096).inverse().unwrap();
    from_fn(|k| {
        let (m, j) = (k / 4, k % 4);
        if j < 3 {
            Expr::var(digits[m][j])
        } else {
            (Expr::var(limbs[m])
                - Expr::var(digits[m][0])
                - Expr::from(16u32) * Expr::var(digits[m][1])
                - Expr::from(256u32) * Expr::var(digits[m][2]))
                * Expr::constant(inv4096)
        }
    })
}

pub(crate) fn control_register<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) -> (Variable, Variable) {
    grouped_control_register(cs, None)
}

pub(crate) const REGISTERS_READ_TIMESTAMP_GROUP: u8 = 0;

pub(crate) fn read_timestamp_distance<F: PrimeField>(calls: Expr<F>) -> Expr<F> {
    Expr::from(common_constants::TIMESTAMP_STEP as u32) * calls
}

pub(crate) fn set_registers_read_timestamp_distance<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    execute: Variable,
) {
    use common_constants::delegation_types::keccak_f1600::KECCAK_F1600_REGISTER_READ_DISTANCE;
    cs.set_read_timestamp_group_distance(
        REGISTERS_READ_TIMESTAMP_GROUP,
        read_timestamp_distance(
            Expr::from(KECCAK_F1600_REGISTER_READ_DISTANCE as u32) * Expr::var(execute),
        ),
    );
}

pub(crate) fn grouped_control_register<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    read_timestamp_group: Option<u8>,
) -> (Variable, Variable) {
    let x10 = cs.request_register_and_indirect_memory_accesses(
        RegisterAccessRequest {
            register_index: CONTROL_REGISTER as u32,
            register_write: true,
            read_timestamp_group,
            indirects_alignment_log2: 0,
            indirect_accesses: vec![],
        },
        "x10 control register read/write",
        2,
    );
    let RegisterAccessType::Write {
        read_value: control,
        write_value: control_next,
    } = x10.register_access
    else {
        unreachable!()
    };
    cs.add_constraint_expr_allow_explicit_linear(Expr::var(control[1]));
    cs.add_constraint_expr_allow_explicit_linear(Expr::var(control_next[1]));
    (control[0], control_next[0])
}

// lanes at `indices` (u64 slots of the x11 state), written where `writes` is set and read-only
// elsewhere; returns the read and written u16 limbs, the written ones aliasing the read ones on
// read-only lanes
pub(crate) fn state_lanes<F: PrimeField, CS: Circuit<F>, const N: usize>(
    cs: &mut CS,
    indices: [Variable; N],
    writes: [bool; N],
) -> ([[Variable; 4]; N], [[Variable; 4]; N]) {
    grouped_state_lanes(cs, indices, writes, None, [None; N])
}

pub(crate) fn grouped_state_lanes<F: PrimeField, CS: Circuit<F>, const N: usize>(
    cs: &mut CS,
    indices: [Variable; N],
    writes: [bool; N],
    register_read_timestamp_group: Option<u8>,
    lane_read_timestamp_groups: [Option<u8>; N],
) -> ([[Variable; 4]; N], [[Variable; 4]; N]) {
    let accesses = (0..N)
        .flat_map(|slot| {
            [0, 4].map(|offset_constant| IndirectAccessOffset {
                variable_dependent: Some((core::mem::size_of::<u64>() as u32, indices[slot])),
                offset_constant,
                assume_no_alignment_overflow: true,
                is_write_access: writes[slot],
                read_timestamp_group: lane_read_timestamp_groups[slot],
            })
        })
        .collect();
    let x11 = cs.request_register_and_indirect_memory_accesses(
        RegisterAccessRequest {
            register_index: STATE_REGISTER as u32,
            register_write: false,
            read_timestamp_group: register_read_timestamp_group,
            indirects_alignment_log2: 8,
            indirect_accesses: accesses,
        },
        "x11 indirect access",
        2,
    );
    assert_eq!(x11.indirect_accesses.len(), 2 * N);
    let mut lanes_in = [[Variable::placeholder_variable(); 4]; N];
    let mut lanes_out = lanes_in;
    for (word, access) in x11.indirect_accesses.iter().enumerate() {
        let (slot, half) = (word / 2, word % 2);
        let (read_value, write_value) = match *access {
            IndirectAccessType::Read { read_value, .. } => (read_value, read_value),
            IndirectAccessType::Write {
                read_value,
                write_value,
                ..
            } => {
                cs.set_values(move |placer: &mut CS::WitnessPlacer| {
                    if CS::ASSUME_MEMORY_VALUES_ASSIGNED {
                        placer.assume_assigned(write_value[0]);
                        placer.assume_assigned(write_value[1]);
                    } else {
                        let value =
                            placer.get_oracle_u32(Placeholder::DelegationIndirectWriteValue {
                                register_index: STATE_REGISTER,
                                word_index: word,
                            });
                        placer.assign_u32_from_u16_parts(write_value, &value);
                    }
                });
                (read_value, write_value)
            }
        };
        lanes_in[slot][2 * half..2 * half + 2].copy_from_slice(&read_value);
        lanes_out[slot][2 * half..2 * half + 2].copy_from_slice(&write_value);
    }
    (lanes_in, lanes_out)
}

// key of the index tables: the control word, plus the execute flag on real rows. The control tables
// key on (control, execute) as two columns instead, which pins x10 to a valid control on real rows
// and to 0 on padding rows
pub(crate) fn control_key<F: PrimeField>(control: Variable, execute: Variable) -> Expr<F> {
    Expr::var(control) + Expr::from(KECCAK_F1600_CONTROL_EXECUTE_FLAG) * Expr::var(execute)
}
