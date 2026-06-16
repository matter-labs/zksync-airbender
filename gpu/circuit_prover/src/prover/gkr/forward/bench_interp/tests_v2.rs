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

use gkr_eval_isa::compiler_v2::gather::{DecoderSpec, GatherDescriptor};
use gkr_eval_isa::eval_ref::{lift, Bf, Ext};
use gkr_eval_isa::interp_v2::{execute2, GatherTables, MatrixSlotData, SourceBanks};
use gkr_eval_isa::isa_v2::encode::encode2;
use gkr_eval_isa::isa_v2::{
    ArithOp, Dst, Header, IndirectKind, Instr2, LdcSub, MemTup, Operand, Program2, RoutineId,
    SPECIAL_ONE,
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

const MEM_TABLE: usize = 64; // mapped-gather value-table length

fn desc(kind: IndirectKind, field_ext: bool) -> GatherDescriptor {
    GatherDescriptor {
        kind,
        field_ext,
        n_slot: None,
        mapping_slot: None,
        n_len: None,
        decoder: None,
        inits_td_set_idx: None,
    }
}

/// Build the memtup + gather program. Slots as in `build_program` (0 ext in,
/// 1 base in, 2 ext out). Gathers: desc0 = RowIndexedSetupE4, desc1 =
/// MappedGenericE4.
fn build_program_memtup_gather() -> Program2 {
    use Operand::*;
    let m = |routine: RoutineId, n: u8| Header::Macro { routine: routine as u8, n_operands: n };
    let cst = |idx: u16| Ldc { sub: LdcSub::Const, idx };
    let instrs = vec![
        // 1. MemoryTuple (id 19): IsRam arm (payload = base col s1c0), roles
        //    [(ADDR_LOW, s0c0), (TS_LOW, s0c1)], const [(MT_CONST_ADDR_LOW, c0)].
        Instr2 {
            header: m(RoutineId::MemoryTuple, 2),
            operands: vec![],
            dsts: vec![Dst::Materialize { slot: 2, col: 0 }],
            memtup: Some(MemTup {
                roles: vec![(0, Affine { slot: 0, col: 0 }), (2, Affine { slot: 0, col: 1 })],
                as_arm: 3, // IsRam
                as_payload: Some(Affine { slot: 1, col: 0 }),
                consts: vec![(64, cst(0))],
            }),
            memtup2: None,
        },
        // 2. GrandProductWithoutCaches (id 14): tuple0 (Constant arm c1, role
        //    [(ADDR_LOW, s0c0)]) * tuple1 (Empty arm, roles [(ADDR_HIGH, s0c1),
        //    (VAL_LOW, s0c2)]). Header n_operands ignored for two-tuple.
        Instr2 {
            header: m(RoutineId::GrandProductWithoutCaches, 3),
            operands: vec![],
            dsts: vec![Dst::Materialize { slot: 2, col: 1 }],
            memtup: Some(MemTup {
                roles: vec![(0, Affine { slot: 0, col: 0 })],
                as_arm: 1, // Constant
                as_payload: Some(cst(1)),
                consts: vec![],
            }),
            memtup2: Some(MemTup {
                roles: vec![(1, Affine { slot: 0, col: 1 }), (4, Affine { slot: 0, col: 2 })],
                as_arm: 0, // Empty
                as_payload: None,
                consts: vec![],
            }),
        },
        // 3. VectorizedLookupSetup (id 18): single RowIndexedSetupE4 gather n[gid].
        Instr2 {
            header: m(RoutineId::VectorizedLookupSetup, 1),
            operands: vec![Indirect { e4: true, desc: 0 }],
            dsts: vec![Dst::Materialize { slot: 2, col: 2 }],
            memtup: None,
            memtup2: None,
        },
        // 4. VectorizedLookup (id 17) with a MAPPED gather column: one group
        //    [term_count=1, const_k(c0), coeff(c1), col(Indirect desc1)].
        Instr2 {
            header: m(RoutineId::VectorizedLookup, 4),
            operands: vec![
                Ldc { sub: LdcSub::Special, idx: SPECIAL_ONE },
                cst(0),
                cst(1),
                Indirect { e4: true, desc: 1 },
            ],
            dsts: vec![Dst::Materialize { slot: 2, col: 3 }],
            memtup: None,
            memtup2: None,
        },
    ];
    Program2 { instrs, consts: vec![7u32, 13u32], n_slot_cells: 0, n_matrix_slots: 3 }
}

const N_OUT_COLS_MG: usize = 4;

#[test]
#[cfg(not(no_cuda))]
fn v2_interp_staged_parity_memtup_gather() {
    let context = make_test_context(256, 32);
    let mut rng = StdRng::seed_from_u64(0x5202_0002u64);
    let program = build_program_memtup_gather();
    let lanes = encode2(&program);
    let gathers = vec![desc(IndirectKind::RowIndexedSetupE4, true), desc(IndirectKind::MappedGenericE4, true)];

    // staged matrix columns: slot0 3 ext, slot1 2 base.
    let s0: Vec<Vec<Ext>> = (0..3).map(|_| (0..T).map(|_| rand_ext(&mut rng)).collect()).collect();
    let s1: Vec<Vec<Bf>> = (0..2).map(|_| (0..T).map(|_| rand_bf(&mut rng)).collect()).collect();

    // gather tables.
    let n0: Vec<Ext> = (0..T).map(|_| rand_ext(&mut rng)).collect(); // RowIndexedSetupE4
    let n1: Vec<Ext> = (0..MEM_TABLE).map(|_| rand_ext(&mut rng)).collect(); // MappedGenericE4 table
    let map1: Vec<u32> = (0..T).map(|_| (rng.gen::<u32>() % MEM_TABLE as u32)).collect();

    // challenges.
    let gamma = rand_ext(&mut rng);
    let perm: Vec<Ext> = (0..6).map(|_| rand_ext(&mut rng)).collect();
    let perm_additive = rand_ext(&mut rng);

    // CPU golden.
    let mut expected: Vec<Vec<Ext>> = vec![vec![Ext::ZERO; T]; N_OUT_COLS_MG];
    for gid in 0..T {
        let gt = GatherTables {
            n: vec![n0.clone(), n1.clone()],
            mapping: vec![vec![], map1.clone()],
            n_len: vec![Some(T), None],
            decoder_mask: vec![None, None],
            alpha_powers: vec![],
        };
        let sb = SourceBanks {
            matrix: vec![
                MatrixSlotData { field_ext: true, columns: vec![s0[0][gid], s0[1][gid], s0[2][gid]] },
                MatrixSlotData { field_ext: false, columns: vec![lift(s1[0][gid]), lift(s1[1][gid])] },
                MatrixSlotData { field_ext: true, columns: vec![] },
            ],
            consts: program.consts.clone(),
            const_challenge: vec![Ext::ZERO; 4],
            arg_challenge: vec![],
            gamma,
            perm_challenges: perm.clone(),
            perm_additive,
            gather_tables: gt,
            gid,
        };
        let res = execute2(&program, &gathers, &sb);
        for ((slot, col), v) in res.materialized {
            assert_eq!(slot, 2);
            expected[col as usize][gid] = v;
        }
    }

    // device staging.
    let lanes_dev = upload(&context, &lanes);
    let consts_mont: Vec<BF> = program.consts.iter().map(|&c| BF::from_u32_with_reduction(c)).collect();
    let consts_dev = upload(&context, &consts_mont);
    let cc_dev = upload(&context, &vec![E4::ZERO; 4]);
    let mut scalars = [E4::ZERO; 8];
    scalars[0] = gamma;
    for r in 0..6 {
        scalars[1 + r] = perm[r];
    }
    scalars[7] = perm_additive;
    let scalars_dev = upload(&context, &scalars);

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

    // gather device buffers.
    let n0_dev = upload(&context, &n0);
    let n1_dev = upload(&context, &n1);
    let map1_dev = upload(&context, &map1);
    let desc_kind_dev = upload(&context, &[3u8, 1u8]);
    let desc_n_host: Vec<u64> = vec![n0_dev.as_ptr() as u64, n1_dev.as_ptr() as u64];
    let desc_n_dev = upload(&context, &desc_n_host);
    let desc_mapping_host: Vec<u64> = vec![0u64, map1_dev.as_ptr() as u64];
    let desc_mapping_dev = upload(&context, &desc_mapping_host);
    let desc_n_len_dev = upload(&context, &[T as u32, 0xFFFF_FFFFu32]);
    let desc_mask_dev = upload(&context, &[0u64, 0u64]);
    let desc_fill_alpha_dev = upload(&context, &[0u32, 0u32]);
    let desc_table_id_dev = upload(&context, &[0u32, 0u32]);

    let out_dev: Vec<DeviceAllocation<E4>> = (0..N_OUT_COLS_MG).map(|_| upload(&context, &vec![E4::ZERO; T])).collect();
    let out_base: Vec<u32> = vec![0, 0, 0, N_OUT_COLS_MG as u32];
    let out_base_dev = upload(&context, &out_base);
    let out_cols_host: Vec<u64> = out_dev.iter().map(|c| c.as_ptr() as u64).collect();
    let out_cols_dev = upload(&context, &out_cols_host);

    let mut err_dev = upload(&context, &[0u32]);

    let dsc = InterpDesc2 {
        program_ldg: lanes_dev.as_ptr(),
        program_lanes: lanes.len() as u32,
        n_instr: program.instrs.len() as u32,
        columns: columns_dev.as_ptr() as *const *const u8,
        col_base: col_base_dev.as_ptr(),
        slot_is_e4: 0b001 | 0b100,
        n_matrix_slots: 3,
        consts: consts_dev.as_ptr(),
        const_challenge: cc_dev.as_ptr(),
        n_const_challenge: 4,
        arg_challenge: ptr::null(),
        n_arg_challenge: 0,
        challenge_scalars: scalars_dev.as_ptr(),
        n_descs: 2,
        desc_kind: desc_kind_dev.as_ptr(),
        desc_n: desc_n_dev.as_ptr() as *const *const u8,
        desc_mapping: desc_mapping_dev.as_ptr() as *const *const u32,
        desc_n_len: desc_n_len_dev.as_ptr(),
        desc_mask: desc_mask_dev.as_ptr() as *const *const BF,
        desc_fill_alpha: desc_fill_alpha_dev.as_ptr(),
        desc_table_id: desc_table_id_dev.as_ptr(),
        out_columns: out_cols_dev.as_ptr() as *const *mut u8,
        out_base: out_base_dev.as_ptr(),
        out_is_e4: 0b100,
        budget_cells: 0,
        count: T as u32,
        error_flag: err_dev.as_mut_ptr(),
    };

    launch_bench_fwd_interp_v2(&dsc, InterpResidency::Ldg, BenchThreads::T128, &context).unwrap();

    let mut err_host = [0u32];
    memory_copy_async(&mut err_host, &err_dev, context.get_exec_stream()).unwrap();
    let mut got: Vec<Vec<E4>> = vec![vec![E4::ZERO; T]; N_OUT_COLS_MG];
    for (col, dev) in out_dev.iter().enumerate() {
        memory_copy_async(&mut got[col], dev, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();

    assert_eq!(err_host[0], 0, "kernel error_flag set: 0x{:x}", err_host[0]);
    for col in 0..N_OUT_COLS_MG {
        for gid in 0..T {
            assert_eq!(got[col][gid], expected[col][gid], "mismatch at output col {col} row {gid}");
        }
    }
}

/// Staged parity for the DecoderMappedE4 gather — the one gather kind tests #1/#2
/// never covered (it surfaced as the add_sub real-fixture residual). Program:
/// `GateOutputFold[Indirect(decoder)]` (1 operand → α^0·gather = the gather
/// value). Stages a value table + mapping + a decoder mask with BOTH zero
/// (disabled → fill) and non-zero (enabled → mapped) rows + an α-power bank, runs
/// `execute2` per row and the kernel over all rows, asserts bit-exact. Isolates
/// the kernel's decoder math (fill formula, mask polarity, mapped read) from the
/// real-fixture device binding.
#[test]
#[cfg(not(no_cuda))]
fn v2_interp_staged_parity_decoder() {
    let context = make_test_context(256, 32);
    let mut rng = StdRng::seed_from_u64(0x5202_0003u64);

    const P: u16 = 2; // fill_alpha_power
    const TID: u32 = 5; // table_id
    const NT: usize = 64; // decoder value-table length

    let program = Program2 {
        instrs: vec![Instr2 {
            header: Header::Macro { routine: RoutineId::GateOutputFold as u8, n_operands: 1 },
            operands: vec![Operand::Indirect { e4: true, desc: 0 }],
            dsts: vec![Dst::Materialize { slot: 2, col: 0 }],
            memtup: None,
            memtup2: None,
        }],
        consts: vec![],
        n_slot_cells: 0,
        n_matrix_slots: 3,
    };
    let lanes = encode2(&program);
    let gathers = vec![GatherDescriptor {
        kind: IndirectKind::DecoderMappedE4,
        field_ext: true,
        n_slot: None,
        mapping_slot: None,
        n_len: None,
        decoder: Some(DecoderSpec { fill_alpha_power: P, table_id: TID }),
        inits_td_set_idx: None,
    }];

    // decoder tables: value table, per-row mapping, and a mask that is base-ZERO
    // on ~1/3 of rows (fill path) and non-zero elsewhere (mapped path).
    let n: Vec<Ext> = (0..NT).map(|_| rand_ext(&mut rng)).collect();
    let mapping: Vec<u32> = (0..T).map(|_| rng.gen::<u32>() % NT as u32).collect();
    let mask: Vec<Bf> =
        (0..T).map(|gid| if gid % 3 == 0 { Bf::ZERO } else { rand_bf(&mut rng) }).collect();
    // α-power bank [1, a, a^2, …, a^P].
    let alpha = rand_ext(&mut rng);
    let alpha_powers: Vec<Ext> = {
        let mut v = vec![Ext::ONE; P as usize + 1];
        let mut acc = Ext::ONE;
        for k in 1..=P as usize {
            acc.mul_assign(&alpha);
            v[k] = acc;
        }
        v
    };

    // CPU golden.
    let mut expected = vec![Ext::ZERO; T];
    for gid in 0..T {
        let gt = GatherTables {
            n: vec![n.clone()],
            mapping: vec![mapping.clone()],
            n_len: vec![None],
            decoder_mask: vec![Some(mask.clone())],
            alpha_powers: alpha_powers.clone(),
        };
        let sb = SourceBanks {
            matrix: vec![
                MatrixSlotData { field_ext: true, columns: vec![] },
                MatrixSlotData { field_ext: false, columns: vec![] },
                MatrixSlotData { field_ext: true, columns: vec![] },
            ],
            consts: vec![],
            const_challenge: alpha_powers.clone(),
            arg_challenge: vec![],
            gamma: Ext::ZERO,
            perm_challenges: vec![Ext::ZERO; 6],
            perm_additive: Ext::ZERO,
            gather_tables: gt,
            gid,
        };
        let res = execute2(&program, &gathers, &sb);
        for ((slot, col), v) in res.materialized {
            assert_eq!((slot, col), (2, 0));
            expected[gid] = v;
        }
    }

    // device staging.
    let lanes_dev = upload(&context, &lanes);
    let consts_dev = upload(&context, &[BF::ZERO]);
    let cc_dev = upload(&context, &alpha_powers);
    let scalars_dev = upload(&context, &[E4::ZERO; 8]);
    let n_dev = upload(&context, &n);
    let mapping_dev = upload(&context, &mapping);
    let mask_dev = upload(&context, &mask);
    let desc_kind_dev = upload(&context, &[2u8]); // DecoderMappedE4
    let desc_n_dev = upload(&context, &[n_dev.as_ptr() as u64]);
    let desc_mapping_dev = upload(&context, &[mapping_dev.as_ptr() as u64]);
    let desc_n_len_dev = upload(&context, &[0xFFFF_FFFFu32]);
    let desc_mask_dev = upload(&context, &[mask_dev.as_ptr() as u64]);
    let desc_fill_alpha_dev = upload(&context, &[P as u32]);
    let desc_table_id_dev = upload(&context, &[TID]);

    let col_base_dev = upload(&context, &[0u32, 0, 0, 0]);
    let columns_dev = upload(&context, &[0u64]);
    let out_dev = upload(&context, &vec![E4::ZERO; T]);
    let out_base_dev = upload(&context, &[0u32, 0, 0, 1]);
    let out_cols_dev = upload(&context, &[out_dev.as_ptr() as u64]);
    let mut err_dev = upload(&context, &[0u32]);

    let dsc = InterpDesc2 {
        program_ldg: lanes_dev.as_ptr(),
        program_lanes: lanes.len() as u32,
        n_instr: 1,
        columns: columns_dev.as_ptr() as *const *const u8,
        col_base: col_base_dev.as_ptr(),
        slot_is_e4: 0b100,
        n_matrix_slots: 3,
        consts: consts_dev.as_ptr(),
        const_challenge: cc_dev.as_ptr(),
        n_const_challenge: alpha_powers.len() as u32,
        arg_challenge: ptr::null(),
        n_arg_challenge: 0,
        challenge_scalars: scalars_dev.as_ptr(),
        n_descs: 1,
        desc_kind: desc_kind_dev.as_ptr(),
        desc_n: desc_n_dev.as_ptr() as *const *const u8,
        desc_mapping: desc_mapping_dev.as_ptr() as *const *const u32,
        desc_n_len: desc_n_len_dev.as_ptr(),
        desc_mask: desc_mask_dev.as_ptr() as *const *const BF,
        desc_fill_alpha: desc_fill_alpha_dev.as_ptr(),
        desc_table_id: desc_table_id_dev.as_ptr(),
        out_columns: out_cols_dev.as_ptr() as *const *mut u8,
        out_base: out_base_dev.as_ptr(),
        out_is_e4: 0b100,
        budget_cells: 0,
        count: T as u32,
        error_flag: err_dev.as_mut_ptr(),
    };

    launch_bench_fwd_interp_v2(&dsc, InterpResidency::Ldg, BenchThreads::T128, &context).unwrap();

    let mut err_host = [0u32];
    memory_copy_async(&mut err_host, &err_dev, context.get_exec_stream()).unwrap();
    let mut got = vec![E4::ZERO; T];
    memory_copy_async(&mut got, &out_dev, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();

    assert_eq!(err_host[0], 0, "kernel error_flag set: 0x{:x}", err_host[0]);
    for gid in 0..T {
        assert_eq!(
            got[gid], expected[gid],
            "decoder mismatch at row {gid} ({})",
            if gid % 3 == 0 { "mask=0 -> fill" } else { "mask!=0 -> mapped" }
        );
    }
}

// ===========================================================================
// 5.2 — REAL-WITNESS bit-exact parity gate (spec Phase 5.2).
//
// The staged tests above prove kernel == CPU-golden (execute2) on random data.
// This gate proves kernel == PRODUCTION at real-witness scale: compile each
// stage-3 circuit's L0 forward layer with the v2 compiler, replay the production
// FLAT launchers to populate `fixture.storage` with the real golden, bind the v2
// kernel's matrix tables / gathers / challenge banks to the SAME production
// buffers (lower_v2::build_interp_desc2_real), run the kernel, then compare each
// `Dst::Materialize` output against its resident production storage column at
// rows [0, t-1].
// ===========================================================================

use super::fixture::CircuitFixture;
use super::lower_v2::{
    build_interp_desc2_real, read_golden_bf, read_golden_e4, readback_out_bf, readback_out_e4,
};
use gkr_eval_isa::compiler_v2::{compile_forward_v2, FwdParams2};
use gkr_design_space::import::load_circuit;
use serial_test::serial;

/// 5.2 — real-witness bit-exact parity for the v2 forward interpreter kernel
/// (`#[ignore]`, GPU). For each stage-3 circuit at layer 0: build the production
/// fixture, replay the flat forward launchers (the golden), compile the v2
/// forward program, bind the kernel to the real production tables, launch
/// LDG/128, read back every materialized output, and assert it equals the
/// resident production FLAT golden at rows [0, t-1]. Non-vacuous (>= 1 output
/// compared per circuit) and `error_flag == 0`.
///
/// COMPILE-ONLY in this phase: the test body is authored correctly but is NOT
/// executed here (it runs later on GPU via `.agents/bin/with_gpu_lock.sh`).
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial]
fn v2_real_fixture_parity() {
    use super::fixture::STAGE3_CIRCUITS;

    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    // Collect per-circuit failures and report them all at the end, so one GPU
    // run surfaces the parity status of EVERY stage-3 circuit (not just the
    // first to mismatch).
    let mut circuit_failures: Vec<String> = Vec::new();

    for circuit in STAGE3_CIRCUITS {
        let loaded =
            load_circuit(&dir.join(format!("{circuit}_codegen_ir_gkr.json"))).unwrap();
        let fixture = CircuitFixture::build(circuit);
        assert!(!fixture.layers.is_empty(), "{circuit}: fixture has no layers");
        assert_eq!(
            loaded.circuit.layers.len(),
            fixture.compiled_circuit.layers.len(),
            "{circuit}: codegen IR vs artifact layer count"
        );

        let layer_idx = 0usize;
        let context = fixture.context();
        let t = fixture.trace_len;

        // (1) Production FLAT golden: replay every captured launch of L0 into
        // `fixture.storage` (the same kernels the flat path runs; idempotent).
        fixture
            .replay_layer_count(layer_idx, t)
            .unwrap_or_else(|e| panic!("{circuit}: replay_layer_count failed: {e:?}"));

        // (2) Compile the v2 forward program for this layer.
        let cg_layer = &loaded.circuit.layers[layer_idx];
        let g = &loaded.graphs[layer_idx];
        let cf2 = compile_forward_v2(cg_layer, g, FwdParams2::default());

        // (3) Bind the kernel to the REAL production tables.
        let mut setup = build_interp_desc2_real(&fixture, layer_idx, &cf2, cg_layer);

        // Surface any gather binding gap loudly (a launcher-deferred kind that
        // could not be resolved from the fixture). A non-empty list means the
        // bit-exact compare below may not cover those gathers' consumers.
        for gap in &setup.unbound_gathers {
            println!("{circuit} L{layer_idx}: GATHER GAP: {gap}");
        }
        if !setup.unbound_gathers.is_empty() {
            circuit_failures.push(format!(
                "{circuit} L{layer_idx}: {} unbound gather(s):\n{}",
                setup.unbound_gathers.len(),
                setup.unbound_gathers.join("\n"),
            ));
            continue;
        }

        println!(
            "{circuit} L{layer_idx}: {} slots, {} lanes, {} materialize outputs",
            setup.n_matrix_slots,
            setup.n_lanes,
            setup.out_columns.len(),
        );

        // (4) Run the kernel (LDG/128) over all rows.
        launch_bench_fwd_interp_v2(&setup.desc, InterpResidency::Ldg, BenchThreads::T128, context)
            .unwrap();

        // (5) Read back the materialized outputs + error flag, snapshot the
        // production goldens, then compare at rows [0, t-1].
        let mut err_host = [0u32];
        memory_copy_async(&mut err_host[..], setup.err_dev(), context.get_exec_stream())
            .unwrap();

        // Read back kernel outputs with the element stride the kernel WROTE:
        // e4 outputs are 16-byte stores (`readback_out_e4`); bf outputs are a
        // contiguous 4-byte bf column (`readback_out_bf`) — reading a bf output
        // back as E4 would read byte `row*16` while the kernel wrote it at byte
        // `row*4`, matching only at row 0 (silent parity failure at row t-1).
        let mut kernel_e4: Vec<Option<Vec<E4>>> = Vec::with_capacity(setup.out_columns.len());
        let mut kernel_bf: Vec<Option<Vec<BF>>> = Vec::with_capacity(setup.out_columns.len());
        for oc in &setup.out_columns {
            if oc.e4 {
                kernel_e4.push(Some(readback_out_e4(&oc.buf, t, context)));
                kernel_bf.push(None);
            } else {
                kernel_bf.push(Some(readback_out_bf(&oc.buf, t, context)));
                kernel_e4.push(None);
            }
        }
        // Production goldens, resolved through the resident storage column.
        let mut golden_bf: Vec<Option<Vec<BF>>> = Vec::with_capacity(setup.out_columns.len());
        let mut golden_e4: Vec<Option<Vec<E4>>> = Vec::with_capacity(setup.out_columns.len());
        for oc in &setup.out_columns {
            let (is_e4, ptr) = fixture.storage_column(oc.golden_addr).unwrap_or_else(|| {
                panic!(
                    "{circuit} L{layer_idx}: materialize output addr {:?} not resident in storage",
                    oc.golden_addr
                )
            });
            assert_eq!(
                is_e4, oc.e4,
                "{circuit} L{layer_idx}: output (slot {}, col {}) storage width vs slot field",
                oc.slot, oc.col
            );
            if oc.e4 {
                golden_e4.push(Some(read_golden_e4(ptr, t, context)));
                golden_bf.push(None);
            } else {
                golden_bf.push(Some(read_golden_bf(ptr, t, context)));
                golden_e4.push(None);
            }
        }
        context.get_exec_stream().synchronize().unwrap();

        if err_host[0] != 0 {
            circuit_failures.push(format!(
                "{circuit} L{layer_idx}: kernel error_flag set: 0x{:x}",
                err_host[0]
            ));
            continue;
        }

        // Non-vacuity: must compare SOMETHING.
        if setup.out_columns.is_empty() {
            circuit_failures.push(format!(
                "{circuit} L{layer_idx}: no materialize outputs to compare (vacuous gate)"
            ));
            continue;
        }

        let rows = [0usize, t - 1];
        let mut n_mismatch = 0usize;
        let mut sample: Vec<String> = Vec::new();
        for (oi, oc) in setup.out_columns.iter().enumerate() {
            for &row in &rows {
                let (got_s, want_s) = if oc.e4 {
                    let want = golden_e4[oi].as_ref().unwrap()[row];
                    let got = kernel_e4[oi].as_ref().unwrap()[row];
                    if got == want {
                        continue;
                    }
                    (format!("{got:?}"), format!("{want:?}"))
                } else {
                    let want = golden_bf[oi].as_ref().unwrap()[row];
                    let got = kernel_bf[oi].as_ref().unwrap()[row];
                    if got == want {
                        continue;
                    }
                    (format!("{got:?}"), format!("{want:?}"))
                };
                n_mismatch += 1;
                if sample.len() < 12 {
                    sample.push(format!(
                        "(slot {}, col {}) row {row} golden {:?}: kernel {got_s} vs prod {want_s}",
                        oc.slot, oc.col, oc.golden_addr
                    ));
                }
            }
        }
        if n_mismatch == 0 {
            println!(
                "{circuit} L{layer_idx}: PASS ({} outputs compared)",
                setup.out_columns.len()
            );
        } else {
            circuit_failures.push(format!(
                "{circuit} L{layer_idx}: {n_mismatch} mismatch(es) over {} outputs x2 rows (sample):\n  {}",
                setup.out_columns.len(),
                sample.join("\n  ")
            ));
        }
    }

    assert!(
        circuit_failures.is_empty(),
        "v2 real-fixture parity: {} circuit(s) FAILED:\n{}",
        circuit_failures.len(),
        circuit_failures.join("\n---\n")
    );
}
