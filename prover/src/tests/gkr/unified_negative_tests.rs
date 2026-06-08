use super::orchestration::common::{run_vm_and_capture, ProgramConfig};
use super::{check_lookups_in_range, *};
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver, evaluate_gkr_witness_for_executor_family,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use ::field::baby_bear::base::BabyBearField;
use ::field::Field;
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use cs::gkr_circuits::unified_reduced_machine::{
    FAMILY_1_FLAG_OFFSET, FAMILY_2_FLAG_OFFSET, FAMILY_4_LW_BIT, FAMILY_4_SW_BIT,
    UNIFIED_REDUCED_MACHINE_NUM_FLAGS,
};
use riscv_transpiler::replayer::*;
use riscv_transpiler::vm::*;
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
use worker::Worker;

const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;

const USE_GKR_WITH_CACHES: bool = cfg!(not(feature = "no_caches"));

fn find_base_layer_address(circuit: &GKRCircuitArtifact<BabyBearField>, name: &str) -> GKRAddress {
    for (var, var_name) in circuit.variable_names.iter() {
        if var_name == name {
            let addr = *circuit
                .placement_data
                .get(var)
                .expect("variable_names entry missing from placement_data");
            return match addr {
                GKRAddress::BaseLayerWitness(_) | GKRAddress::BaseLayerMemory(_) => addr,
                other => panic!("variable '{name}' not in the base layer: {other:?}"),
            };
        }
    }
    panic!("no variable named '{name}' in unified circuit artifact");
}

fn read_cell(
    trace: &GKRFullWitnessTrace<BabyBearField, Global, Global>,
    addr: GKRAddress,
    row: usize,
) -> BabyBearField {
    match addr {
        GKRAddress::BaseLayerWitness(col) => trace.column_major_witness_trace[col][row],
        GKRAddress::BaseLayerMemory(col) => trace.column_major_memory_trace[col][row],
        other => panic!("not a base-layer address: {other:?}"),
    }
}

fn write_cell(
    trace: &mut GKRFullWitnessTrace<BabyBearField, Global, Global>,
    addr: GKRAddress,
    row: usize,
    value: BabyBearField,
) {
    match addr {
        GKRAddress::BaseLayerWitness(col) => trace.column_major_witness_trace[col][row] = value,
        GKRAddress::BaseLayerMemory(col) => trace.column_major_memory_trace[col][row] = value,
        other => panic!("not a base-layer address: {other:?}"),
    }
}

fn base_trace_len(trace: &GKRFullWitnessTrace<BabyBearField, Global, Global>) -> usize {
    trace.column_major_witness_trace[0].len()
}

fn build_satisfying_trace_with_mutation(
    mutate: impl FnOnce(
        &GKRCircuitArtifact<BabyBearField>,
        &mut GKRFullWitnessTrace<BabyBearField, Global, Global>,
    ),
) -> (
    GKRCircuitArtifact<BabyBearField>,
    GKRFullWitnessTrace<BabyBearField, Global, Global>,
) {
    type CountersT = DelegationsAndUnifiedCounters;

    let worker = Worker::new_with_num_threads(8);

    let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
        deserialize_from_file("../cs/compiled_circuits/unified_reduced_machine_layout_gkr.json")
    } else {
        deserialize_from_file(
            "../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json",
        )
    };

    let config = ProgramConfig::multi_family_smoke_blake_g_function();
    let vm = run_vm_and_capture::<CountersT>(&config, &worker);

    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    assert!(num_calls < NUM_CYCLES_PER_CHUNK);

    let num_teardown_sets = circuit.memory_layout.teardown_sets.len();
    let mut inits_and_teardowns = Vec::with_capacity(num_teardown_sets);
    for _ in 0..num_teardown_sets {
        let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        inits_and_teardowns.push(([a, b], [c, d]));
    }
    vm.ram
        .collect_inits_and_teardowns_into_columns::<BabyBearField, _>(
            &worker,
            TRACE_LEN_LOG2,
            0,
            &mut inits_and_teardowns,
        );

    // Replay the snapshotter into the unified destination tracer.
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(vm.expected_final_state, state);

    let oracle = UnifiedRiscvCircuitOracle::new::<BabyBearField>(
        &buffer[..],
        &vm.text_section,
        common_constants::ROM_WORD_SIZE,
    );

    let table_driver = build_unified_table_driver::<BabyBearField>(&vm.binary);

    let mut full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
        &circuit,
        super::unified_reduced_machine::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &table_driver,
        &worker,
        Some(inits_and_teardowns),
        Global,
        Global,
    );

    mutate(&circuit, &mut full_trace);

    (circuit, full_trace)
}

/// Force a misaligned `writeaddr_lo` on an SW row.
/// The decomposition `4*top_14 + 2*bit_1 + bit_0 = writeaddr_lo` becomes
/// inconsistent (low bits unchanged, but `writeaddr_lo` no longer matches),
/// so `check_satisfied` rejects.
#[test]
fn misaligned_sw_writeaddr_lo_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let sw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_SW_BIT}]"));
        let writeaddr_lo_addr = find_base_layer_address(circuit, "unified memwrite_addr[0]");
        let sw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, sw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one SW");
        // `0xFFFD` is a 16-bit value with bit 0 = 1 → misaligned. The
        // decomposition constraint (degree 1, ungated) catches it because
        // we leave bit_0/bit_1/top_14 unchanged.
        write_cell(trace, writeaddr_lo_addr, sw_row, BabyBearField::new(0xFFFD));
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected misaligned SW writeaddr_lo mutation to fail check_satisfied"
    );
}

/// one-hot family dispatch. Set a second family bit on an LW row,
/// so two dispatch bits are hot on the same executing row. The setup
/// constraint `is_any_family_active - execute * Σ family-bits = 0` then
/// evaluates to `1 - 1*2 = -1 ≠ 0`, so `check_satisfied` rejects.
#[test]
fn two_family_bits_on_one_row_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let lw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_LW_BIT}]"));
        let sw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_SW_BIT}]"));
        let lw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, lw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one LW");
        // LW row already has family_bit[15] = 1; force family_bit[16] = 1 too.
        write_cell(trace, sw_addr, lw_row, BabyBearField::ONE);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected two-family-bits-on-one-row mutation to fail check_satisfied"
    );
}

/// Pin `rd_write_limbs[1] = 0` when SLT writes rd. The Family-2 rd-write
/// rewrite from standalone's `selected_rd_high = (is_jal+is_jalr)*saved_pc_high`
/// to per-opcode `is_X_writes_rd` helpers lost the implicit
/// `selected_rd_high = 0 for SLT` zeroing; the explicit constraint
/// `is_slt_writes_rd * rd_write_limbs[1] = 0` at jump_branch_slt.rs:786 restores
/// it. This test mutates `rd_write_limbs[1]` on an SLT row to a 16-bit non-zero
/// value (so the top-level RC doesn't catch it) and asserts `check_satisfied`
/// rejects — guards against accidental constraint drop in future refactors.
#[test]
fn slt_rd_write_high_limb_nonzero_rejected() {
    // Family 2's SLT sub-opcode is bit 2 within Family 2's bitmask (per
    // jump_branch_slt_family/decoder.rs:6 `const SLT_BIT: usize = 2`).
    let slt_bit_index = FAMILY_2_FLAG_OFFSET + 2;
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let slt_addr = find_base_layer_address(circuit, &format!("family_bit[{}]", slt_bit_index));
        let rd_write_hi_addr = find_base_layer_address(circuit, "rd/mem write write_value[1]");
        let slt_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, slt_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one SLT");
        // 16-bit non-zero so the implicit top-level RC doesn't catch it; only
        // the explicit `is_slt_writes_rd * rd_write_limbs[1] = 0` constraint should.
        write_cell(trace, rd_write_hi_addr, slt_row, BabyBearField::new(0x1234));
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected SLT rd_write_limbs[1] = 0x1234 mutation to fail check_satisfied"
    );
}

/// SW-into-ROM trap: the constraint `is_rom * is_sw = 0` forbids stores to ROM
/// addresses. Mutating `is_rom = 1` on an SW row should make the product 1 ≠ 0;
/// `check_satisfied` must reject. `is_rom` is aliased into the shared scratch-Boolean
/// pool (slot 2) — on an SW row that slot holds `is_rom`.
#[test]
fn sw_into_rom_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let sw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_SW_BIT}]"));
        let is_rom_addr = find_base_layer_address(circuit, "shared scratch bool[2]");
        let sw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, sw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one SW");
        write_cell(trace, is_rom_addr, sw_row, BabyBearField::ONE);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected is_rom=1 on SW row to fail check_satisfied (is_rom * is_sw = 0 trap)"
    );
}

/// Family-4 `ram_addr` select-trick binding. `ram_addr` is aliased into the shared
/// scratch-Variable pool (slots 0,1) and bound by `is_lw*(ram_addr-readaddr)=0` +
/// `is_sw*(ram_addr-writeaddr)=0`. On an LW row `ram_addr[0]` must equal the read
/// address low limb; corrupting the pooled slot breaks the gated constraint, so
/// `check_satisfied` must reject — proving the select-trick rewrite still binds
/// ram_addr on Family-4 rows.
#[test]
fn unified_ram_addr_corruption_on_lw_row_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let lw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_LW_BIT}]"));
        // ram_addr[0] aliases shared scratch var[0].
        let ram_addr_lo = find_base_layer_address(circuit, "shared scratch var[0]");
        let lw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, lw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one LW");
        let cur = read_cell(trace, ram_addr_lo, lw_row);
        write_cell(trace, ram_addr_lo, lw_row, cur + BabyBearField::ONE);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected ram_addr[0] corruption on LW row to fail check_satisfied (select-trick binding)"
    );
}

/// Family-4 SW-alignment pooled-bool binding. `bit_0` is aliased into the shared
/// scratch-Boolean pool (slot 3). On an SW row the address is word-aligned so
/// `bit_0 = 0`; the is_sw-gated trap `is_sw*(bit_0+bit_1)=0` (and the gated
/// decomposition) pin it. Flipping it to 1 must make `check_satisfied` reject —
/// proving the is_sw-gated decomposition still binds bit_0 on SW rows.
#[test]
fn unified_sw_align_bit0_flip_on_sw_row_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let sw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_SW_BIT}]"));
        // sw-align bit_0 aliases shared scratch bool[3].
        let bit_0_addr = find_base_layer_address(circuit, "shared scratch bool[3]");
        let sw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, sw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one SW");
        let cur = read_cell(trace, bit_0_addr, sw_row);
        let flipped = if cur == BabyBearField::ZERO {
            BabyBearField::ONE
        } else {
            BabyBearField::ZERO
        };
        write_cell(trace, bit_0_addr, sw_row, flipped);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected sw-align bit_0 flip on SW row to fail check_satisfied (gated alignment trap)"
    );
}

/// Empty family mask on an executing row: clear ALL family bits on a row that
/// has `execute = 1`. The decoder lookup (gated by `execute`) will see the row
/// claim a bitmask of all zeros, which doesn't match any committed decoder
/// table entry. `check_satisfied` should reject via the decoder lookup
/// mismatch (or the dispatch one-hot constraint, depending on which fires first
/// in the evaluator).
#[test]
fn empty_family_mask_on_executing_row_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        // Find an executing row by looking for any row where at least one
        // dispatch bit is set (LW or SW serve as anchors; multi_family_smoke
        // executes both).
        let lw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_LW_BIT}]"));
        let exec_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, lw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one LW");
        // Clear every family bit on this row (17 bits in the unified layout).
        for bit in 0..cs::gkr_circuits::unified_reduced_machine::UNIFIED_REDUCED_MACHINE_NUM_FLAGS {
            let addr = find_base_layer_address(circuit, &format!("family_bit[{}]", bit));
            write_cell(trace, addr, exec_row, BabyBearField::ZERO);
        }
        // Also clear is_any_family_active so the dispatch one-hot setup
        // (`is_any_family_active - execute * Σbits = 0`) is locally consistent
        // — the rejection then comes from the decoder lookup mismatch (the
        // committed table doesn't have an entry mapping this PC to all-zero
        // family bits), not from a trivially-failing arithmetic constraint
        // that's incidental to the actual attack.
        let any_active_addr = find_base_layer_address(circuit, "unified family-dispatch one-hot");
        write_cell(trace, any_active_addr, exec_row, BabyBearField::ZERO);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected empty family mask on executing row to fail check_satisfied"
    );
}

/// Range-check-16 violation that the existing arithmetic-only
/// [`check_satisfied`] cannot see. Picks an RC-16 lookup expression that is a
/// trivial single-input (`1 * single_addr + 0`), writes a 17-bit sentinel
/// (`0x12345 = 74565`) into the referenced cell at row 0, and asserts the
/// new [`check_lookups_in_range`] oracle rejects.
///
/// `check_satisfied` may or may not also catch the mutation — depends on
/// whether the target cell appears in a degree-1/degree-2 arithmetic
/// constraint as well as the RC-16 lookup. The test logs both verdicts but
/// only the lookup-oracle assertion is load-bearing. The point is that the
/// lookup oracle catches a class of attacks (range overflow) that the
/// arithmetic oracle is documented to skip.
#[test]
fn range_check_16_violation_caught_by_lookup_oracle() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        // Find any RC-16 lookup whose input is a trivial `1 * single_addr + 0`.
        // Those are the cleanest single-cell targets — corrupting the addr makes
        // the lookup expression evaluate to exactly the new cell value.
        let target_addr = circuit
            .range_check_16_lookup_expressions
            .iter()
            .find_map(|l| {
                if l.input.is_trivial_single_input() {
                    Some(l.input.linear_terms[0].1)
                } else {
                    None
                }
            })
            .expect("expected at least one trivial single-input RC-16 lookup");

        // 0x12345 = 74565, the smallest 17-bit value. Field-element-valid
        // (well under BabyBear's ~2^31 modulus); range-check-invalid.
        write_cell(trace, target_addr, 0, BabyBearField::new(0x12345));
    });

    let arith_ok = check_satisfied(&circuit, &full_trace);
    let lookup_ok = check_lookups_in_range(&circuit, &full_trace);
    println!(
        "range_check_16_violation: check_satisfied = {}, check_lookups_in_range = {}",
        arith_ok, lookup_ok
    );
    assert!(
        !lookup_ok,
        "expected check_lookups_in_range to reject a 17-bit value in an RC-16 column"
    );
}

/// Cross-family flag collision. Sets a bit from
/// Family 1 (ADD, bit 0) AND a bit from Family 2 (JAL, bit 8) hot on the same
/// executing row. The unified dispatch one-hot constraint at
/// `circuit.rs:393-408` (`is_any_family_active - execute * Σ family-dispatch-bits = 0`,
/// with `is_any_family_active` Boolean) forces the sum across families to be in
/// {0, 1} on executing rows. Two cross-family bits set ⇒ sum ≥ 2 ⇒ the Boolean
/// is_any_family_active can't satisfy. `check_satisfied` must reject.
#[test]
fn cross_family_flag_collision_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        // Anchor on an LW row (we know multi_family_smoke executes some).
        // Pre-mutation that row has only `family_bit[FAMILY_4_LW_BIT]` hot.
        let lw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_LW_BIT}]"));
        let f1_bit_addr =
            find_base_layer_address(circuit, &format!("family_bit[{FAMILY_1_FLAG_OFFSET}]"));
        let f2_bit_addr =
            find_base_layer_address(circuit, &format!("family_bit[{FAMILY_2_FLAG_OFFSET}]"));
        let lw_addr_clear = lw_addr;
        let lw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, lw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one LW");
        // Clear the LW bit and set bits in BOTH F1 and F2 dispatch ranges.
        // The dispatch one-hot constraint sums across families, so this is the
        // genuine cross-family collision (vs LW+SW which are both inside F4).
        write_cell(trace, lw_addr_clear, lw_row, BabyBearField::ZERO);
        write_cell(trace, f1_bit_addr, lw_row, BabyBearField::ONE);
        write_cell(trace, f2_bit_addr, lw_row, BabyBearField::ONE);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected cross-family flag collision (F1+F2 bits set) to fail check_satisfied"
    );
}

/// Padding-row family-bit leak: on a padding row (`execute = 0`), the decoder
/// lookup is gated off, so the bitmask is NOT bound to a decoder table entry.
/// The explicit padding-zero-sum constraint at `circuit.rs:418-432`
/// (`(1 - execute) * Σ all 17 family-bits = 0`) is the only defence against a
/// malicious prover setting a family bit on a padding row. This test mutates a
/// padding row to set `family_bit[0] = 1` and asserts `check_satisfied`
/// rejects. Without that constraint, the prover could claim "extra"
/// instructions of any family on padding rows, breaking the
/// "executed-cycle-count" invariant downstream.
#[test]
fn padding_row_family_bit_set_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        // Padding rows are those with `execute = 0`. Find one. `execute` is
        // committed as a named variable — look it up by name.
        let execute_addr = find_base_layer_address(circuit, "Execute flag for cycle");
        let padding_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, execute_addr, r) == BabyBearField::ZERO)
            .expect("trace must contain at least one padding row (execute = 0)");
        // Set Family 1 bit 0 on this padding row. The constraint
        // `(1 - execute) * Σbits = 0` evaluates to `1 * 1 = 1 ≠ 0` and the
        // arithmetic checker rejects.
        let f1_bit_addr =
            find_base_layer_address(circuit, &format!("family_bit[{FAMILY_1_FLAG_OFFSET}]"));
        write_cell(trace, f1_bit_addr, padding_row, BabyBearField::ONE);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected family_bit[0] = 1 on a padding row to fail check_satisfied"
    );
}

/// Unified-circuit address-carry flip: the `rs1 + imm = ram_addr` addition
/// in Family 4's data path uses a Boolean carry `of_lo` (overflow flag from
/// low limb). Flipping it on an active LW/SW row breaks the decomposition
/// `rs1_lo + imm_lo - ram_addr_lo - 2^16 * of_lo = 0`, so `check_satisfied`
/// rejects.
///
/// `of_lo` is a branch-local scratch Boolean that aliases into the shared
/// scratch-Boolean pool (slot 0), so its committed column is named
/// `"shared scratch bool[0]"` — on an LW row that slot holds `of_lo`.
#[test]
fn unified_address_carry_lo_flip_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let lw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_LW_BIT}]"));
        let of_lo_addr = find_base_layer_address(circuit, "shared scratch bool[0]");
        let lw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, lw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one LW");
        // Flip the Boolean: if of_lo was 0 → set to 1, if 1 → set to 0.
        let cur = read_cell(trace, of_lo_addr, lw_row);
        let flipped = if cur == BabyBearField::ZERO {
            BabyBearField::ONE
        } else {
            BabyBearField::ZERO
        };
        write_cell(trace, of_lo_addr, lw_row, flipped);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected of_lo flip on LW row to fail check_satisfied"
    );
}

/// Family-2 pooled-Boolean binding. `add_rel_1_intermediate_of` (the next-PC
/// addition's intermediate carry) is a branch-local scratch Boolean aliased into
/// the shared scratch-Boolean pool at slot [2] (`"shared scratch bool[2]"`). On a
/// Family-2 row that slot holds the F2 carry; the second add-like constraint
/// (`... - is_slt * 2^16 * add_rel_1_intermediate_of = 0`) ties it to the PC
/// computation. Flipping it on an SLT row breaks that constraint, so
/// `check_satisfied` must reject — proving the pool aliasing did not un-bind the
/// F2 carry on its own family's rows.
#[test]
fn unified_f2_pooled_bool_binds_on_slt_row_rejected() {
    let slt_bit_index = FAMILY_2_FLAG_OFFSET + 2;
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let slt_addr = find_base_layer_address(circuit, &format!("family_bit[{}]", slt_bit_index));
        let bool_addr = find_base_layer_address(circuit, "shared scratch bool[2]");
        let slt_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, slt_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one SLT");
        let cur = read_cell(trace, bool_addr, slt_row);
        let flipped = if cur == BabyBearField::ZERO {
            BabyBearField::ONE
        } else {
            BabyBearField::ZERO
        };
        write_cell(trace, bool_addr, slt_row, flipped);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected pooled F2 carry bool flip on SLT row to fail check_satisfied"
    );
}

/// Family-2 pooled-Variable binding. `should_jump_or_slt_value` (the SLT result /
/// branch decision, a gated lookup output) is aliased into the shared
/// scratch-Variable pool at slot [2] (`"shared scratch var[2]"`). On an SLT row
/// with `rd != 0` the rd-write low constraint pins
/// `is_slt_writes_rd * should_jump_or_slt_value = ... * rd_write_limbs[0]`, so
/// corrupting the slot breaks it (the same first-SLT-row anchor the
/// `slt_rd_write_high_limb_nonzero_rejected` test relies on guarantees
/// `rd != 0`). `check_satisfied` must reject — proving the Variable-pool aliasing
/// did not un-bind the F2 lookup output on its own family's rows.
#[test]
fn unified_f2_pooled_var_binds_on_slt_row_rejected() {
    let slt_bit_index = FAMILY_2_FLAG_OFFSET + 2;
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let slt_addr = find_base_layer_address(circuit, &format!("family_bit[{}]", slt_bit_index));
        let var_addr = find_base_layer_address(circuit, "shared scratch var[2]");
        let slt_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, slt_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one SLT");
        let cur = read_cell(trace, var_addr, slt_row);
        write_cell(trace, var_addr, slt_row, cur + BabyBearField::ONE);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected pooled F2 should_jump_or_slt_value corruption on SLT row to fail check_satisfied"
    );
}

/// F4's `top_14` (SW-align `writeaddr_lo >> 2`) borrows limb 0 of the
/// shared F1/F2/F4 RC-16 Register on F4 rows. On an SW row that slot holds
/// `top_14`, pinned by the is_sw-gated decomposition `4*top_14 + 2*bit_1 + bit_0
/// = writeaddr_lo`. Corrupting the pooled slot on an SW row breaks the
/// decomposition, so `check_satisfied` must reject — proving the RC-16-Register
/// aliasing did not un-bind `top_14` on F4's own rows.
#[test]
fn unified_top14_pooled_corruption_on_sw_row_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let sw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_SW_BIT}]"));
        // top_14 aliases limb 0 of the shared F1/F2/F4 intermediate Register.
        let top14_addr = find_base_layer_address(circuit, "shared F1/F2 intermediate reg[0]");
        let sw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, sw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one SW");
        let cur = read_cell(trace, top14_addr, sw_row);
        write_cell(trace, top14_addr, sw_row, cur + BabyBearField::ONE);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected pooled top_14 corruption on SW row to fail check_satisfied (gated decomposition)"
    );
}
