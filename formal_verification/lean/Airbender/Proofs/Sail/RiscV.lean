import Airbender.Proofs.AddSub.SailContract
import Airbender.Proofs.Sail.Sequential
import Mathlib.Tactic.IntervalCases

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open Airbender.Arithmetic
open _root_.Sail.ArchSem

theorem write_callback_pure (reg : SailRV32.regidx) (value : BitVec 32) :
    SailRV32.Functions.xreg_write_callback reg value = pure () := by
  cases reg
  simp [SailRV32.Functions.xreg_write_callback, SailRV32.Functions.reg_name_forwards,
    SailRV32.Functions.encdec_reg_forwards_matches, SailRV32.Functions.get_config_use_abi_names,
    SailRV32.not, SailRV32.Functions.xreg_full_write_callback, freeM_pure_bind]

private theorem primitive_write (reg : SailRV32.Register) (value : SailRV32.RegisterType reg)
    (state : State) :
    run (do SailRV32.writeReg reg value; pure ()) state =
      .ok () { state with regs := state.regs.insert reg value } := rfl

private theorem run_pure (state : State) :
    run (pure () : SailRV32.SailM Unit) state = .ok () state := rfl

theorem write_success (rd : SailRV32.regidx) (value : BitVec 32) (state : State) :
    ∃ after, run (SailRV32.Functions.wX_bits rd value) state = .ok () after := by
  cases rd with
  | Regidx bits =>
    have hb : bits.toNat < 32 := bits.isLt
    change ∃ after, run (SailRV32.Functions.wX (.Regno (bits.toNat : Int)) value) state = _
    interval_cases bits.toNat <;>
      simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
        write_callback_pure, freeM_pure_bind, primitive_write, run_pure]

/-- Internal execution-only relation, used to compose destination and PC effects. -/
def destinationSpec (input : Input) (output : Word) : Prop :=
  ∃ after,
    run (execution input) input.before = .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
    run (writeResult input.rd output) input.before = .ok SailRV32.Functions.RETIRE_SUCCESS after

/-- Sail's actual x0 accessor discards the value and performs no state update. -/
theorem write_zero (value : BitVec 32) :
    SailRV32.Functions.wX_bits zeroRegister value = pure () := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, _root_.Sail.BitVec.toNatInt,
    freeM_pure_bind]

/-- An original instruction writing x0 leaves the state unchanged, even when its
    circuit operands were replaced by zero. Only successful original reads are required. -/
theorem spec_zero_write {input : Input} {output : Word} (hc : Contract input)
    (hz : input.rd = zeroRegister) : destinationSpec input output := by
  have executed : run (execution input) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS input.before := by
    cases hop : input.row.opcode
    · obtain ⟨left, hl, _⟩ := hc.leftRead (by simp [hop])
      obtain ⟨right, hr, _⟩ := hc.rightRead (by simp [hop])
      simp only [execution, instruction, registerClause, hop, SailRV32.Functions.execute_RTYPE, hz,
        freeM_bind_assoc, freeM_pure_bind, Option.get_some]
      rw [run_bind_of_ok _ _ _ _ _ hl, run_bind_of_ok _ _ _ _ _ hr]
      rw [write_zero, freeM_pure_bind]
      rfl
    · obtain ⟨left, hl, _⟩ := hc.leftRead (by simp [hop])
      simp only [execution, instruction, registerClause, hop, SailRV32.Functions.execute_ITYPE, hz,
        freeM_bind_assoc, freeM_pure_bind, Option.get_some]
      rw [run_bind_of_ok _ _ _ _ _ hl, write_zero, freeM_pure_bind]
      rfl
    · obtain ⟨left, hl, _⟩ := hc.leftRead (by simp [hop])
      obtain ⟨right, hr, _⟩ := hc.rightRead (by simp [hop])
      simp only [execution, instruction, registerClause, hop, SailRV32.Functions.execute_RTYPE, hz,
        freeM_bind_assoc, freeM_pure_bind, Option.get_some]
      rw [run_bind_of_ok _ _ _ _ _ hl, run_bind_of_ok _ _ _ _ _ hr]
      rw [write_zero, freeM_pure_bind]
      rfl
    · simp only [execution, instruction, registerClause, hop, SailRV32.Functions.execute_UTYPE, hz,
        freeM_pure_bind, write_zero, Option.get_some]
      rfl
    · have hp := hc.pcRead
      simp only [execution, instruction, registerClause, hop, SailRV32.Functions.execute_UTYPE, hz,
        freeM_bind_assoc, freeM_pure_bind, Option.get_some]
      rw [run_bind_of_ok _ _ _ _ _ hp, write_zero, freeM_pure_bind]
      rfl
  refine ⟨input.before, executed, ?_⟩
  rw [writeResult, hz, write_zero, freeM_pure_bind]
  rfl

/-- Connect a proved result equation to the actual generated execution clauses.
    This lemma introduces no separate instruction-specification relation. -/
theorem spec_of_result {input : Input} {output : Word} (hc : Contract input)
    (nonzero : input.rd ≠ zeroRegister)
    (h : output.toBitVec = match input.row.opcode with
      | .add => input.row.left.toBitVec + input.row.right.toBitVec
      | .addi => input.row.left.toBitVec + input.row.immediate.toBitVec
      | .sub => input.row.left.toBitVec - input.row.right.toBitVec
      | .lui => input.row.immediate.toBitVec
      | .auipc => input.row.pc.toBitVec + input.row.immediate.toBitVec) :
    destinationSpec input output := by
  have leftRead (condition : input.row.opcode = .add ∨ input.row.opcode = .addi ∨ input.row.opcode = .sub) :
      run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.row.left.toBitVec input.before := by
    obtain ⟨value, read, mapping⟩ := hc.leftRead condition
    simpa only [mapping nonzero] using read
  have rightRead (condition : input.row.opcode = .add ∨ input.row.opcode = .sub) :
      run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.row.right.toBitVec input.before := by
    obtain ⟨value, read, mapping⟩ := hc.rightRead condition
    simpa only [mapping nonzero] using read
  have pcRead (_condition : input.row.opcode = .auipc) :
      run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.row.pc.toBitVec input.before := by
    exact hc.pcRead
  have he : run (execution input) input.before = run (writeResult input.rd output) input.before := by
    unfold execution writeResult
    cases hop : input.row.opcode
    · simp only [instruction, registerClause, Option.get_some, hop, SailRV32.Functions.execute_RTYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ (leftRead (by simp [hop]))]
      rw [run_bind_of_ok _ _ _ _ _ (rightRead (by simp [hop]))]
      rw [← h]
    · simp only [instruction, registerClause, Option.get_some, hop, SailRV32.Functions.execute_ITYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ (leftRead (by simp [hop]))]
      rw [← hc.signExtension nonzero hop, ← h]
    · simp only [instruction, registerClause, Option.get_some, hop, SailRV32.Functions.execute_RTYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ (leftRead (by simp [hop]))]
      rw [run_bind_of_ok _ _ _ _ _ (rightRead (by simp [hop]))]
      rw [← h]
    · simp only [instruction, registerClause, Option.get_some, hop, SailRV32.Functions.execute_UTYPE, freeM_pure_bind] at h ⊢
      rw [← hc.upperImmediate nonzero (by simp [hop]), ← h]
    · simp only [instruction, registerClause, Option.get_some, hop, SailRV32.Functions.execute_UTYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ (pcRead hop)]
      rw [← hc.upperImmediate nonzero (by simp [hop]), ← h]
  obtain ⟨after, hw⟩ := write_success input.rd output.toBitVec input.before
  have hw' : run (writeResult input.rd output) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    unfold writeResult
    rw [run_bind_of_ok _ _ _ _ _ hw]
    rfl
  exact ⟨after, he.trans hw', hw'⟩

/-- Sail's actual integer truncation is native word construction for naturals. -/
theorem truncate_nat (width n : Nat) :
    SailRV32.Functions.to_bits_truncate (l := width) (n : Int) = BitVec.ofNat width n := by
  apply BitVec.eq_of_toNat_eq
  simp [SailRV32.Functions.to_bits_truncate, _root_.Sail.get_slice_int, Nat.pow_succ]

private theorem low_int (sourceWidth width : Nat) (h : width ≤ sourceWidth) (n : Int) :
    (BitVec.ofInt sourceWidth n).extractLsb' 0 width = BitVec.ofInt width n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_zero]
  have positive : (0 : Int) < (2 ^ width : Nat) := by exact_mod_cast Nat.two_pow_pos width
  have positiveBig : (0 : Int) < (2 ^ sourceWidth : Nat) := by exact_mod_cast Nat.two_pow_pos sourceWidth
  have convert := Int.toNat_emod (Int.emod_nonneg n (ne_of_gt positiveBig)) (le_of_lt positive)
  simp only [Int.toNat_natCast] at convert
  rw [← convert]
  congr 1
  apply Int.emod_emod_of_dvd
  exact_mod_cast Nat.pow_dvd_pow 2 h

theorem truncate_int (width : Nat) (n : Int) :
    SailRV32.Functions.to_bits_truncate (l := width) n = BitVec.ofInt width n := by
  simpa only [SailRV32.Functions.to_bits_truncate, _root_.Sail.get_slice_int] using
    low_int (0 + width + 1) width (by omega) n

theorem mul_low_signed (x y : BitVec 32) :
    SailRV32.Functions.mult_to_bits_half .Signed .Signed x y .Low = x * y := by
  simp only [SailRV32.Functions.mult_to_bits_half]
  rw [truncate_int]
  change (BitVec.ofInt 64 (x.toInt * y.toInt)).extractLsb' 0 32 = x * y
  rw [low_int 64 32 (by decide), BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

theorem mul_high_unsigned (x y : BitVec 32) :
    SailRV32.Functions.mult_to_bits_half .Unsigned .Unsigned x y .High =
      BitVec.ofNat 32 ((x.toNat * y.toNat) / 4294967296) := by
  simp only [SailRV32.Functions.mult_to_bits_half, Sail.BitVec.toNatInt]
  change (SailRV32.Functions.to_bits_truncate (l := 64)
    ((x.toNat : Int) * (y.toNat : Int))).extractLsb' 32 32 = _
  rw [← Int.natCast_mul, Sail.truncate_nat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  have productBound : x.toNat * y.toNat < 2^64 := by
    have := Nat.mul_le_mul (Nat.le_sub_one_of_lt x.isLt) (Nat.le_sub_one_of_lt y.isLt)
    norm_num at this ⊢
    omega
  rw [Nat.mod_eq_of_lt productBound, Nat.shiftRight_eq_div_pow]

end Airbender.Reference.RiscV.Sail
