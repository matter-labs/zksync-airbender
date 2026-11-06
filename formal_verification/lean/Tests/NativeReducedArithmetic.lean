import Airbender.Review.Circuits.ReducedMachine.ArithmeticTheorems

namespace Tests.NativeReducedArithmetic
open Airbender Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Arithmetic
open Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native reduced masks intentionally differ from the standalone arithmetic masks. -/
theorem masks : (#[ArithmeticMode.add.mask,ArithmeticMode.addi.mask,ArithmeticMode.sub.mask,
    ArithmeticMode.lui.mask,ArithmeticMode.auipc.mask] : Array Nat) = #[11,9,8195,513,17] := by decide +kernel

/-- Immediate arithmetic still consumes the native readonly rs2 query; it is not
    replaced with the selected immediate or a RAM access. -/
theorem immediate_port {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = 9) : source2 w = #v[w 9,w 10] ∧ w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 := by
  have route := arithmetic_routing holds .addi mask
  exact ⟨route.1,route.2.1,route.2.2.1,route.2.2.2.1⟩

theorem ram_source_rejected {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ArithmeticMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) : w 88 ≠ 0 := by
  rw [(NativeArithmeticFieldProofs.source_port holds mode mask).2.2]
  decide

/-- Candidate scalar bounds do not require a supplied source/read range. -/
theorem oversized_add_candidate_rejected {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = 11) : (candidateWord w).lo < 65536 ∧ (candidateWord w).hi < 65536 :=
  NativeArithmeticResultProofs.candidate_bounds holds .add mask (by intro h; cases h)

/-- Discarding a write does not discard its candidate or native arithmetic checks. -/
theorem discarded_write {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ArithmeticMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus))
    (zero : rdZeroFlag w = 1) : rdWrite w = #v[0,0] := by
  rw [(NativeArithmeticFieldProofs.write holds mode mask).2]
  simp [zero,arithmeticCandidate]

private theorem inputs {w : Nat → ZMod mersenne31Modulus}
    (source : sourceWord w = ⟨65535,65535⟩) (operand : operandWord w = ⟨1,0⟩)
    (pc : initialPCWord w = ⟨65535,65535⟩) (imm : arithmeticImmediateWord w = ⟨1,0⟩) :
    (sourceWord w).Bounded ∧ (operandWord w).Bounded ∧
      (initialPCWord w).Bounded ∧ (arithmeticImmediateWord w).Bounded := by
  rw [source,operand,pc,imm]
  norm_num [Word.Bounded,limbBase]

/-- Complete native acceptance implies RV32 low/high carry and wrap, not field
    reduction of the complete 32-bit result. This is a conditional row check. -/
theorem add_wrap {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = 11)
    (source : sourceWord w = ⟨65535,65535⟩) (operand : operandWord w = ⟨1,0⟩)
    (pc : initialPCWord w = ⟨65535,65535⟩) (imm : arithmeticImmediateWord w = ⟨1,0⟩) :
    (candidateWord w).toBitVec = 0 := by
  have b := inputs source operand pc imm
  have result := NativeArithmeticResultProofs.candidate_result holds .add mask b.1 b.2.1 b.2.2.1 b.2.2.2
  rw [source,operand] at result
  simpa [ArithmeticMode.result,Word.toBitVec,Word.value,limbBase] using result

/-- AUIPC retains a full RV32 wrap using the actual incoming PC/immediate fields. -/
theorem auipc_wrap {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = 17)
    (source : sourceWord w = ⟨65535,65535⟩) (operand : operandWord w = ⟨1,0⟩)
    (pc : initialPCWord w = ⟨61440,65535⟩) (imm : arithmeticImmediateWord w = ⟨4096,0⟩) :
    (candidateWord w).toBitVec = 0 := by
  have b : (sourceWord w).Bounded ∧ (operandWord w).Bounded ∧
      (initialPCWord w).Bounded ∧ (arithmeticImmediateWord w).Bounded := by
    rw [source,operand,pc,imm]
    norm_num [Word.Bounded,limbBase]
  have result := NativeArithmeticResultProofs.candidate_result holds .auipc mask b.1 b.2.1 b.2.2.1 b.2.2.2
  rw [pc,imm] at result
  simpa [ArithmeticMode.result,Word.toBitVec,Word.value,limbBase] using result

/-- Native SUB retains its borrow convention and full high word. -/
theorem sub_borrow {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = 8195) (source : sourceWord w = ⟨0,0⟩)
    (operand : operandWord w = ⟨1,0⟩) (pc : (initialPCWord w).Bounded)
    (imm : (arithmeticImmediateWord w).Bounded) :
    (candidateWord w).toBitVec = BitVec.ofNat 32 4294967295 := by
  have sb : (sourceWord w).Bounded := by rw [source]; norm_num [Word.Bounded,limbBase]
  have ob : (operandWord w).Bounded := by rw [operand]; norm_num [Word.Bounded,limbBase]
  have result := NativeArithmeticResultProofs.candidate_result holds .sub mask sb ob pc imm
  rw [source,operand] at result
  simpa [ArithmeticMode.result,Word.toBitVec,Word.value,limbBase] using result

/-- LUI retains a high RV32 word larger than the base-field modulus. -/
theorem lui_high_word {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = 513) (source : (sourceWord w).Bounded)
    (operand : (operandWord w).Bounded) (pc : (initialPCWord w).Bounded)
    (imm : arithmeticImmediateWord w = ⟨0,65535⟩) :
    (candidateWord w).toBitVec = BitVec.ofNat 32 4294901760 := by
  have ib : (arithmeticImmediateWord w).Bounded := by rw [imm]; norm_num [Word.Bounded,limbBase]
  have result := NativeArithmeticResultProofs.candidate_result holds .lui mask source operand pc ib
  rw [imm] at result
  simpa [ArithmeticMode.result,Word.toBitVec,Word.value,limbBase] using result

end Tests.NativeReducedArithmetic
