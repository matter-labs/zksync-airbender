import Airbender.Review.AddSub.Artifact
import Airbender.Review.Properties
import Airbender.Review.Field
import Airbender.Review.AddSub.Modular
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Constraints
import Airbender.Proofs.Sail.PC
import Airbender.Proofs.AddSub.PC

namespace Airbender.AddSub.Proofs
open Airbender.Arithmetic

/-- The shared comparison equations force a canonical BabyBear result on every
    modular branch. No operand bounds or arithmetic-result premise is used. -/
theorem modular_canonical_output {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (s10 : w 10 = 0) (s11 : w 11 = 0) (s12 : w 12 = 0)
    (selected : w 13 + w 14 + w 15 + w 16 = 1) :
    (w 33).val + 65536 * (w 34).val < babyBearModulus := by
  have borrow := Verification.assertion_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.constraints]⟩
  have low := Verification.assertion_of_holds h
    ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have carry := Verification.assertion_of_holds h
    ⟨25, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, s10, s11, s12, selected] at borrow low high carry
  have b : w 40 = 1 := by linear_combination -borrow
  have boolean : w 39 * (w 39 - 1) = 0 := by
    simpa [mul_eq_zero, sub_eq_add_neg] using carry
  obtain ⟨c, cb, hc⟩ := boolean_nat boolean
  have rlo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨0, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have rhi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨1, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have olo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨2, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have ohi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at rlo rhi olo ohi
  have lowEq : (((w 37).val : Nat) : ZMod p) + 1 =
      (w 33).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc] at low
    linear_combination low
  have highEq : (c : ZMod p) + (w 38).val + 30720 = (w 34).val + 65536 := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc, b] at high
    linear_combination high
  exact Word.lt_of_borrow (output := ⟨(w 33).val, (w 34).val⟩)
    (remainder := ⟨(w 37).val, (w 38).val⟩) (modulus := ⟨1, 30720⟩)
    hp ⟨olo, ohi⟩ ⟨by decide, by decide⟩ ⟨rlo, rhi⟩ cb
    (by simpa using lowEq) (by simpa using highEq)

/-- All four custom arithmetic cases reuse the same canonical-output proof and
    shared soundness property. The fixed BabyBear artifact supplies Montgomery R^-1. -/
theorem modular_result {input : Modular.Input} {output : Reference.RiscV.Sail.Output}
    {w : Nat → ZMod babyBearModulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (interfaces : Modular.InterfaceAssumptions input output w)
    (mapping : Modular.WordMapping input output w) (nonzero : input.rd ≠ Reference.RiscV.Sail.zeroRegister) :
    output.destination.value = (Modular.arithmeticResult input.opcode input.left input.right input.oldDestination).val := by
  have s10 := interfaces.selection 10 (by omega) (by omega)
  have s11 := interfaces.selection 11 (by omega) (by omega)
  have s12 := interfaces.selection 12 (by omega) (by omega)
  have s13 := interfaces.selection 13 (by omega) (by omega)
  have s14 := interfaces.selection 14 (by omega) (by omega)
  have s15 := interfaces.selection 15 (by omega) (by omega)
  have s16 := interfaces.selection 16 (by omega) (by omega)
  have nonstandard : w 10 = 0 ∧ w 11 = 0 ∧ w 12 = 0 := by
    cases hop : input.opcode <;> simp [hop, nonzero, Modular.Opcode.selector] at s10 s11 s12
    all_goals exact ⟨s10, s11, s12⟩
  have selected : w 13 + w 14 + w 15 + w 16 = 1 := by
    cases hop : input.opcode <;>
      simp [hop, nonzero, Modular.Opcode.selector] at s13 s14 s15 s16
    all_goals simp [s13, s14, s15, s16]
  have canonical : output.destination.value < babyBearModulus := by
    simpa [Word.value, limbBase, mapping.outputLo, mapping.outputHi] using
      modular_canonical_output (by decide) constraints nonstandard.1 nonstandard.2.1
        nonstandard.2.2 selected
  have outputCast : (output.destination.value : ZMod babyBearModulus) = w 33 + 65536 * w 34 := by
    simp [Word.value, limbBase, mapping.outputLo, mapping.outputHi]
  have intermediate := Verification.assertion_of_holds constraints
    ⟨1, by simp [importedConstraints, FlatOperation.constraints]⟩
  have result := Verification.assertion_of_holds constraints
    ⟨2, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mapping.left nonzero, mapping.right nonzero] at intermediate result
  have inverse : (943718400 : ZMod babyBearModulus) = (4294967296 : ZMod babyBearModulus)⁻¹ := by
    have unit : (943718400 : ZMod babyBearModulus) * 4294967296 = 1 := by decide
    have nonzero : (4294967296 : ZMod babyBearModulus) ≠ 0 := by decide
    calc
      (943718400 : ZMod babyBearModulus) =
          943718400 * (4294967296 * (4294967296 : ZMod babyBearModulus)⁻¹) := by
        rw [mul_inv_cancel₀ nonzero, mul_one]
      _ = _ := by rw [← mul_assoc, unit, one_mul]
  unfold Modular.arithmeticResult
  rw [← ZMod.val_natCast_of_lt canonical]
  apply congrArg ZMod.val
  rw [outputCast]
  cases hop : input.opcode <;>
    simp [hop, nonzero, Modular.Opcode.selector] at s13 s14 s15 s16 ⊢
  · simp [s13, s14, s15, s16] at result
    linear_combination result + mapping.right nonzero
  · simp [s13, s14, s15, s16] at result
    linear_combination result
  · simp [s13, s14, s15, s16] at result intermediate
    rw [← inverse]
    linear_combination result - intermediate
  · simp [s13, s14, s15, s16, mapping.oldDestination nonzero hop] at result intermediate
    rw [← inverse]
    linear_combination result - intermediate

private theorem modular_contract_nextPC {input : Modular.Input}
    (hc : Modular.RegisterContract input) (pc : BitVec 32) :
    Modular.RegisterContract { input with before :=
      { input.before with regs := input.before.regs.insert .nextPC pc } } := by
  constructor
  · obtain ⟨value, read, mapping⟩ := hc.leftRead
    exact ⟨value, Reference.RiscV.Sail.rX_nextPC input.rs1 read, mapping⟩
  · obtain ⟨value, read, mapping⟩ := hc.rightRead
    exact ⟨value, Reference.RiscV.Sail.rX_nextPC input.rs2 read, mapping⟩
  · intro nonzero condition
    exact Reference.RiscV.Sail.rX_nextPC input.rd (hc.oldRead nonzero condition)
  · exact Reference.RiscV.Sail.read_register_nextPC pc (by decide) hc.pcRead

private theorem modular_destination {input : Modular.Input} {output : Word}
    (hc : Modular.RegisterContract input)
    (result : input.rd ≠ Reference.RiscV.Sail.zeroRegister → output.value =
      (Modular.arithmeticResult input.opcode input.left input.right input.oldDestination).val) :
    ∃ after,
      Reference.Sail.run (Modular.execution input) input.before =
        .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
      Reference.Sail.run (Reference.RiscV.Sail.writeResult input.rd output) input.before =
        .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  open Reference.Sail Reference.RiscV.Sail in
    obtain ⟨left, hl, ml⟩ := hc.leftRead
    obtain ⟨right, hr, mr⟩ := hc.rightRead
    by_cases hz : input.rd = zeroRegister
    · refine ⟨input.before, ?_, ?_⟩
      · simp only [Modular.execution, freeM_pure_bind]
        rw [run_bind_of_ok _ _ _ _ _ hl, run_bind_of_ok _ _ _ _ _ hr]
        cases input.opcode <;> simp only [freeM_pure_bind, hz, write_zero] <;> rfl
      · rw [writeResult, hz, write_zero, freeM_pure_bind]
        rfl
    · have bitResult : output.toBitVec = BitVec.ofNat 32
          (Modular.arithmeticResult input.opcode input.left input.right input.oldDestination).val := by
        change BitVec.ofNat 32 output.value = _
        rw [result hz]
      rw [ml hz] at hl
      rw [mr hz] at hr
      have executed : run (Modular.execution input) input.before =
          run (writeResult input.rd output) input.before := by
        simp only [Modular.execution, writeResult, freeM_pure_bind]
        rw [run_bind_of_ok _ _ _ _ _ hl, run_bind_of_ok _ _ _ _ _ hr]
        cases hop : input.opcode
        all_goals simp only [hop, Modular.arithmeticResult] at bitResult
        all_goals first
          | (simp only [Modular.arithmeticResult]; rw [← bitResult])
          | (rw [run_bind_of_ok _ _ _ _ _ (hc.oldRead hz hop)]
             simp only [Modular.arithmeticResult]
             rw [← bitResult])
      obtain ⟨after, hw⟩ := write_success input.rd output.toBitVec input.before
      have projected : run (writeResult input.rd output) input.before =
          .ok SailRV32.Functions.RETIRE_SUCCESS after := by
        rw [writeResult, run_bind_of_ok _ _ _ _ _ hw]
        rfl
      exact ⟨after, executed.trans projected, projected⟩

/-- Custom arithmetic and native architectural effects share the standard PC
    retirement proof. No operand/result assumption replaces an imported equation. -/
theorem modular_soundness :
    Modular.circuitModel.SoundnessUnder Modular.InterfaceAssumptions Modular.spec := by
  rintro input output w ⟨interfaces, constraints, mapping⟩
  have pc := pc_successor (by decide) (by decide) constraints
    (PCMapping.mk mapping.pcLo mapping.pcHi mapping.finalPCLo mapping.finalPCHi)
    interfaces.initialPCBounds
  apply Reference.RiscV.Sail.retire_of_destination interfaces.registers.pcRead pc.2.2
  apply modular_destination (modular_contract_nextPC interfaces.registers output.pc.toBitVec)
  intro nonzero
  have value := modular_result constraints interfaces mapping nonzero
  exact value

end Airbender.AddSub.Proofs
