module
public import Proven.Trace.Machine.ExtraBits
public import Proven.Trace.Machine.Selectors
public import Human.Trace.Machine.ExternalInput
public import Human.Trace.Machine.Model

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Extra unrolled rows select precisely their decoded delegation or independent-input operation. -/
theorem unrolled_extra_flags {config : RVMachineConfig} {instruction : RV.Instr}
    {entry : RVMachineProgramEntry} {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (fields : rvMachineExtraFields config instruction = some entry.data)
    (query : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    decide (Requests.Selected w) = isCallerInstruction instruction ∧
      NonDeterminism.Pooled.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) = instruction.readsInput := by
  have flags := unrolled_machine_selectors core query (extra_mask_bound fields)
  have bits := extra_instruction_bits fields
  have caller : w 17 = if entry.data.mask.testBit 7 then 1 else 0 := by
    simpa [AddSub.importedConstraintsDecoderColumns] using flags ⟨7, by decide⟩
  have read : w 18 = if entry.data.mask.testBit 8 then 1 else 0 := by
    simpa [AddSub.importedConstraintsDecoderColumns] using flags ⟨8, by decide⟩
  constructor
  · change decide (w 17 = 1) = isCallerInstruction instruction
    rw [caller, bits.1]
    cases isCallerInstruction instruction <;> simp
  · change (w 18 == 1) = instruction.readsInput
    rw [read, bits.2]
    cases instruction.readsInput <;> simp

/-- Extra unified rows use the same decoded operation bits at the imported unified columns. -/
theorem unified_extra_flags {instruction : RV.Instr} {entry : RVMachineProgramEntry}
    {setup : Table (ZMod babyBearModulus) (fields 10)} {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints setup))
    (fields : rvMachineExtraFields .unified instruction = some entry.data)
    (query : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    decide (UnifiedReduced.Caller.Selected w) = isCallerInstruction instruction ∧
      unifiedIsRead (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) = instruction.readsInput := by
  have flags := unified_machine_selectors core query (by have bound := extra_mask_bound fields; omega)
  have bits := extra_instruction_bits fields
  have caller : w 18 = if entry.data.mask.testBit 7 then 1 else 0 := by
    simpa [UnifiedReduced.importedConstraintsDecoderColumns] using flags ⟨7, by decide⟩
  have read : w 19 = if entry.data.mask.testBit 8 then 1 else 0 := by
    simpa [UnifiedReduced.importedConstraintsDecoderColumns] using flags ⟨8, by decide⟩
  constructor
  · change decide (w 18 = 1) = isCallerInstruction instruction
    rw [caller, bits.1]
    cases isCallerInstruction instruction <;> simp
  · change (w 19 == 1) = instruction.readsInput
    rw [read, bits.2]
    cases instruction.readsInput <;> simp

end Airbender.Trace.Machine.Proofs
