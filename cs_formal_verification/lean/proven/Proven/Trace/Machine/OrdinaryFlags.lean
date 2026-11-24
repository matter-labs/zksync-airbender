module
public import Proven.Trace.Machine.OrdinaryMasks
public import Proven.Trace.Machine.Selectors
public import Human.Trace.Machine.ExternalInput
public import Human.Trace.Machine.Model

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- An ordinary unrolled row selects neither the caller path nor an external input read. -/
theorem unrolled_ordinary_flags {setup : PooledSetup babyBearModulus}
    {row : Row babyBearModulus PooledFamily} {entry : RVMachineProgramEntry}
    {ordinary : DecoderData PooledFamily} {instruction : RV.Instr}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup))
    (fields : rvPooledDecoderFields instruction = some ordinary)
    (data : entry.data = RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled) ordinary)
    (family : entry.data.family = .pooled row.family)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    (row.family == .addSub && decide (Requests.Selected row.assignment)) ≠ true ∧
      NonDeterminism.Pooled.isRead row = false := by
  obtain ⟨tag, w⟩ := row
  cases tag
  case addSub =>
    have actualFamily : ordinary.family = .addSub := by
      rw [data] at family
      exact RVMachineDecoderFamily.pooled.inj family
    have bound : entry.data.mask ≤ 4 := by
      rw [data]
      exact pooled_arithmetic_mask_bound fields actualFamily
    have core := Verification.holds_of_sublist constraints
      (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
    have flags := unrolled_machine_selectors core query (by omega)
    have bit7 : entry.data.mask.testBit 7 = false := Nat.testBit_eq_false_of_lt (by omega)
    have bit8 : entry.data.mask.testBit 8 = false := Nat.testBit_eq_false_of_lt (by omega)
    have noCaller : w 17 = 0 := by
      simpa [AddSub.importedConstraintsDecoderColumns, bit7] using flags ⟨7, by decide⟩
    have noRead : w 18 = 0 := by
      simpa [AddSub.importedConstraintsDecoderColumns, bit8] using flags ⟨8, by decide⟩
    constructor
    · simp [Requests.Selected, AddSub.importedConstraintsDecoderColumns, noCaller]
    · change (w 18 == 1) = false
      simp [noRead]
  all_goals simp [NonDeterminism.Pooled.isRead]

/-- An ordinary unified row has zero caller and input-read columns. -/
theorem unified_ordinary_flags {setup : Table (ZMod babyBearModulus) (fields 10)}
    {w : Nat → ZMod babyBearModulus} {entry : RVMachineProgramEntry}
    {ordinary : DecoderData UnifiedFamily} {instruction : RV.Instr}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints setup))
    (fields : UnifiedReduced.rvDecoderFields instruction = some ordinary)
    (data : entry.data = RVMachineDecoderData.ofOrdinary (family := fun _ => .unified) ordinary)
    (query : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus))) :
    ¬ UnifiedReduced.Caller.Selected w ∧ unifiedIsRead (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) = false := by
  have bits := unified_ordinary_mask_bits fields
  have bound : entry.data.mask < 524288 := by
    rw [data]
    exact (UnifiedReduced.Proofs.RV.rv_field_bounds fields).2.1
  have flags := unified_machine_selectors core query bound
  have noCaller : w 18 = 0 := by
    have flag := flags ⟨7, by decide⟩
    rw [data] at flag
    simpa [RVMachineDecoderData.ofOrdinary, UnifiedReduced.importedConstraintsDecoderColumns, bits.1] using flag
  have noRead : w 19 = 0 := by
    have flag := flags ⟨8, by decide⟩
    rw [data] at flag
    simpa [RVMachineDecoderData.ofOrdinary, UnifiedReduced.importedConstraintsDecoderColumns, bits.2] using flag
  constructor
  · change w 18 ≠ 1
    rw [noCaller]
    exact zero_ne_one
  · change (w 19 == 1) = false
    simp [noRead]

end Airbender.Trace.Machine.Proofs
