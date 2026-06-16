//! Staged parity gate for the v2 forward interpreter kernel
//! (`native/bench/gkr_fwd_interp_v2.cu`): build a hand-authored `Program2`
//! exercising the arith family + the gather-free / memtup-free macro routines,
//! stage RANDOM source columns + challenge banks, run the CPU golden model
//! (`gkr_eval_isa::interp_v2::execute2`) per row, run the kernel over all rows,
//! and assert bit-exact equality of every materialized output.
//!
//! This isolates "is the kernel a faithful execute2?" (decode + operand reads +
//! field ops + num/den footers) from device-data binding; the gather + memory-
//! tuple routines and the real-witness-vs-production gate are separate tests.

use super::interp_v2_gpu::{launch_bench_fwd_interp_v2, InterpDesc2};
use super::{BenchThreads, InterpResidency};

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;

use era_cudart::memory::memory_copy_async;

use gkr_eval_isa::eval_ref::{lift, Bf, Ext};
use gkr_eval_isa::interp_v2::{execute2, MatrixSlotData, SourceBanks};
use gkr_eval_isa::isa_v2::encode::encode2;
use gkr_eval_isa::isa_v2::{
    ArithOp, Dst, Header, Instr2, Operand, Program2, RoutineId, SPECIAL_ONE,
};

use field::{Field, FieldExtension, PrimeField};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::ptr;

const T: usize = 256; // rows

fn rand_ext(rng: &mut StdRng) -> Ext {
    <Ext as FieldExtension<Bf>>::from_coeffs([
        Bf::from_u32_with_reduction(rng.gen()),
        Bf::from_u32_with_reduction(rng.gen()),
        Bf::from_u32_with_reduction(rng.gen()),
        Bf::from_u32_with_reduction(rng.gen()),
    ])
}
fn rand_bf(rng: &mut StdRng) -> Bf {
    Bf::from_u32_with_reduction(rng.gen())
}

/// alloc + H2D a host slice; returns the device buffer (kept alive by caller).
fn upload<X: Copy>(context: &ProverContext, host: &[X]) -> DeviceAllocation<X> {
    let mut dev: DeviceAllocation<X> = context.alloc(host.len().max(1), AllocationPlacement::Top).unwrap();
    if !host.is_empty() {
        memory_copy_async(&mut dev[0..host.len()], host, context.get_exec_stream()).unwrap();
    }
    dev
}

/// Build the test program. Slots: 0 = ext input (cols 0,1,2), 1 = base input
/// (cols 0,1), 2 = ext output backing (materialize). Covers Sum/Prod/Dot, the
/// GateOutputFold, Product, MaskIdentity, LookupExtPair (num/den),
/// AggregateLookupPair (num/den), SingleColumnLookup, VectorizedLookup.
fn build_program() -> Program2 {
    use Operand::*;
    let m = |routine: RoutineId, n: u8| Header::Macro { routine: routine as u8, n_operands: n };
    let instrs = vec![
        // 1. Sum [s0c0, s0c1, const0] -> cell0 (e4)
        Instr2 {
            header: Header::Arith { op: ArithOp::Sum, arity: 3 },
            operands: vec![Affine { slot: 0, col: 0 }, Affine { slot: 0, col: 1 }, Ldc { sub: gkr_eval_isa::isa_v2::LdcSub::Const, idx: 0 }],
            dsts: vec![Dst::Slot { e4: true, cell: 0 }],
            memtup: None,
            memtup2: None,
        },
        // 2. Prod [cell0, s0c2] -> cell4 (e4)
        Instr2 {
            header: Header::Arith { op: ArithOp::Prod, arity: 2 },
            operands: vec![Slot { e4: true, cell: 0 }, Affine { slot: 0, col: 2 }],
            dsts: vec![Dst::Slot { e4: true, cell: 4 }],
            memtup: None,
            memtup2: None,
        },
        // 3. Dot arity 2 [(s0c0,s0c1),(s0c2,s1c0)] -> cell8 (e4)
        Instr2 {
            header: Header::Arith { op: ArithOp::Dot, arity: 2 },
            operands: vec![
                Affine { slot: 0, col: 0 }, Affine { slot: 0, col: 1 },
                Affine { slot: 0, col: 2 }, Affine { slot: 1, col: 0 },
            ],
            dsts: vec![Dst::Slot { e4: true, cell: 8 }],
            memtup: None,
            memtup2: None,
        },
        // 4. GateOutputFold [s0c0,s0c1,s0c2] -> (2,0)
        Instr2 {
            header: m(RoutineId::GateOutputFold, 3),
            operands: vec![Affine { slot: 0, col: 0 }, Affine { slot: 0, col: 1 }, Affine { slot: 0, col: 2 }],
            dsts: vec![Dst::Materialize { slot: 2, col: 0 }],
            memtup: None,
            memtup2: None,
        },
        // 5. Product [s0c0,s0c1] -> (2,1)
        Instr2 {
            header: m(RoutineId::Product, 2),
            operands: vec![Affine { slot: 0, col: 0 }, Affine { slot: 0, col: 1 }],
            dsts: vec![Dst::Materialize { slot: 2, col: 1 }],
            memtup: None,
            memtup2: None,
        },
        // 6. MaskIdentity [s0c0(v), s0c1(m)] -> (2,2)
        Instr2 {
            header: m(RoutineId::MaskIdentity, 2),
            operands: vec![Affine { slot: 0, col: 0 }, Affine { slot: 0, col: 1 }],
            dsts: vec![Dst::Materialize { slot: 2, col: 2 }],
            memtup: None,
            memtup2: None,
        },
        // 7. LookupExtPair [b,d] -> num (2,3), den (2,4)
        Instr2 {
            header: m(RoutineId::LookupExtPair, 2),
            operands: vec![Affine { slot: 0, col: 0 }, Affine { slot: 0, col: 1 }],
            dsts: vec![Dst::Materialize { slot: 2, col: 3 }, Dst::Materialize { slot: 2, col: 4 }],
            memtup: None,
            memtup2: None,
        },
        // 8. AggregateLookupPair [a,b,c,d] -> num (2,5), den (2,6)
        Instr2 {
            header: m(RoutineId::AggregateLookupPair, 4),
            operands: vec![
                Affine { slot: 0, col: 0 }, Affine { slot: 0, col: 1 },
                Affine { slot: 0, col: 2 }, Slot { e4: true, cell: 8 },
            ],
            dsts: vec![Dst::Materialize { slot: 2, col: 5 }, Dst::Materialize { slot: 2, col: 6 }],
            memtup: None,
            memtup2: None,
        },
        // 9. SingleColumnLookup [const1, coeff(const0), s1c0] -> (2,7)
        Instr2 {
            header: m(RoutineId::SingleColumnLookup, 3),
            operands: vec![
                Ldc { sub: gkr_eval_isa::isa_v2::LdcSub::Const, idx: 1 },
                Ldc { sub: gkr_eval_isa::isa_v2::LdcSub::Const, idx: 0 },
                Affine { slot: 1, col: 1 },
            ],
            dsts: vec![Dst::Materialize { slot: 2, col: 7 }],
            memtup: None,
            memtup2: None,
        },
        // 10. VectorizedLookup, one group: [term_count=1, const_k(const0), coeff(const1), col(s0c0)] -> (2,8)
        Instr2 {
            header: m(RoutineId::VectorizedLookup, 4),
            operands: vec![
                Ldc { sub: gkr_eval_isa::isa_v2::LdcSub::Special, idx: SPECIAL_ONE },
                Ldc { sub: gkr_eval_isa::isa_v2::LdcSub::Const, idx: 0 },
                Ldc { sub: gkr_eval_isa::isa_v2::LdcSub::Const, idx: 1 },
                Affine { slot: 0, col: 0 },
            ],
            dsts: vec![Dst::Materialize { slot: 2, col: 8 }],
            memtup: None,
            memtup2: None,
        },
    ];
    Program2 {
        instrs,
        consts: vec![7u32, 13u32],
        n_slot_cells: 12,
        n_matrix_slots: 3,
    }
}

const N_OUT_COLS: usize = 9; // slot-2 materialize columns 0..8

#[test]
#[cfg(not(no_cuda))]
fn v2_interp_staged_parity_vs_execute2() {
    let context = make_test_context(256, 32);
    let mut rng = StdRng::seed_from_u64(0x5202_0001u64);
    let program = build_program();
    let lanes = encode2(&program);

    // --- staged host data ---
    // slot 0: 3 ext columns; slot 1: 2 base columns; each length T.
    let s0: Vec<Vec<Ext>> = (0..3).map(|_| (0..T).map(|_| rand_ext(&mut rng)).collect()).collect();
    let s1: Vec<Vec<Bf>> = (0..2).map(|_| (0..T).map(|_| rand_bf(&mut rng)).collect()).collect();

    // alpha-power bank: [unused, a^1, a^2, a^3]; gamma; 6 perm; perm_additive.
    let alpha = rand_ext(&mut rng);
    let const_challenge: Vec<Ext> = {
        let mut v = vec![Ext::ZERO; 4];
        let mut acc = Ext::ONE;
        for k in 1..4 {
            acc.mul_assign(&alpha);
            v[k] = acc;
        }
        v
    };
    let gamma = rand_ext(&mut rng);
    let perm: Vec<Ext> = (0..6).map(|_| rand_ext(&mut rng)).collect();
    let perm_additive = rand_ext(&mut rng);

    // --- CPU golden: execute2 per row, collect expected per output (slot2,col) ---
    let mut expected: Vec<Vec<Ext>> = vec![vec![Ext::ZERO; T]; N_OUT_COLS];
    for gid in 0..T {
        let sb = SourceBanks {
            matrix: vec![
                MatrixSlotData { field_ext: true, columns: vec![s0[0][gid], s0[1][gid], s0[2][gid]] },
                MatrixSlotData { field_ext: false, columns: vec![lift(s1[0][gid]), lift(s1[1][gid])] },
                MatrixSlotData { field_ext: true, columns: vec![] },
            ],
            consts: program.consts.clone(),
            const_challenge: const_challenge.clone(),
            arg_challenge: vec![],
            gamma,
            perm_challenges: perm.clone(),
            perm_additive,
            gather_tables: Default::default(),
            gid,
        };
        let res = execute2(&program, &[], &sb);
        for ((slot, col), v) in res.materialized {
            assert_eq!(slot, 2, "test program materializes only into slot 2");
            expected[col as usize][gid] = v;
        }
    }

    // --- device staging ---
    let lanes_dev = upload(&context, &lanes);
    let consts_mont: Vec<BF> = program.consts.iter().map(|&c| BF::from_u32_with_reduction(c)).collect();
    let consts_dev = upload(&context, &consts_mont);
    let cc_dev = upload(&context, &const_challenge);
    let mut scalars = [E4::ZERO; 8];
    scalars[0] = gamma;
    for r in 0..6 {
        scalars[1 + r] = perm[r];
    }
    scalars[7] = perm_additive;
    let scalars_dev = upload(&context, &scalars);

    // matrix columns: slot0 (3 e4 buffers), slot1 (2 bf buffers). col_base
    // prefix = [0, 3, 5, 5] (slot caps 3,2,0). slot_is_e4 = bit0 set.
    let s0_dev: Vec<DeviceAllocation<E4>> = s0.iter().map(|c| upload(&context, c)).collect();
    let s1_dev: Vec<DeviceAllocation<BF>> = s1.iter().map(|c| upload(&context, c)).collect();
    let col_base: Vec<u32> = vec![0, 3, 5, 5];
    let col_base_dev = upload(&context, &col_base);
    let mut columns_host: Vec<u64> = Vec::new();
    for c in &s0_dev {
        columns_host.push(c.as_ptr() as u64);
    }
    for c in &s1_dev {
        columns_host.push(c.as_ptr() as u64);
    }
    let columns_dev = upload(&context, &columns_host);
    let slot_is_e4: u32 = 0b001 | 0b100; // slot0 ext, slot1 base, slot2 ext

    // output columns: slot2 has N_OUT_COLS e4 buffers; out_base=[0,0,0,N].
    let out_dev: Vec<DeviceAllocation<E4>> = (0..N_OUT_COLS).map(|_| upload(&context, &vec![E4::ZERO; T])).collect();
    let out_base: Vec<u32> = vec![0, 0, 0, N_OUT_COLS as u32];
    let out_base_dev = upload(&context, &out_base);
    let out_cols_host: Vec<u64> = out_dev.iter().map(|c| c.as_ptr() as u64).collect();
    let out_cols_dev = upload(&context, &out_cols_host);
    let out_is_e4: u32 = 0b100;

    let mut err_dev = upload(&context, &[0u32]);

    let desc = InterpDesc2 {
        program_ldg: lanes_dev.as_ptr(),
        program_lanes: lanes.len() as u32,
        n_instr: program.instrs.len() as u32,
        columns: columns_dev.as_ptr() as *const *const u8,
        col_base: col_base_dev.as_ptr(),
        slot_is_e4,
        n_matrix_slots: 3,
        consts: consts_dev.as_ptr(),
        const_challenge: cc_dev.as_ptr(),
        n_const_challenge: const_challenge.len() as u32,
        arg_challenge: ptr::null(),
        n_arg_challenge: 0,
        challenge_scalars: scalars_dev.as_ptr(),
        n_descs: 0,
        desc_kind: ptr::null(),
        desc_field_e4: 0,
        desc_n: ptr::null(),
        desc_mapping: ptr::null(),
        desc_n_len: ptr::null(),
        desc_mask: ptr::null(),
        desc_fill_alpha: ptr::null(),
        desc_table_id: ptr::null(),
        out_columns: out_cols_dev.as_ptr() as *const *mut u8,
        out_base: out_base_dev.as_ptr(),
        out_is_e4,
        budget_cells: program.n_slot_cells as u32,
        count: T as u32,
        error_flag: err_dev.as_mut_ptr(),
    };

    launch_bench_fwd_interp_v2(&desc, InterpResidency::Ldg, BenchThreads::T128, &context).unwrap();

    // readback
    let mut err_host = [0u32];
    memory_copy_async(&mut err_host, &err_dev, context.get_exec_stream()).unwrap();
    let mut got: Vec<Vec<E4>> = vec![vec![E4::ZERO; T]; N_OUT_COLS];
    for (col, dev) in out_dev.iter().enumerate() {
        memory_copy_async(&mut got[col], dev, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();

    assert_eq!(err_host[0], 0, "kernel error_flag set: 0x{:x}", err_host[0]);
    for col in 0..N_OUT_COLS {
        for gid in 0..T {
            assert_eq!(
                got[col][gid], expected[col][gid],
                "mismatch at output col {col} row {gid}"
            );
        }
    }
}
