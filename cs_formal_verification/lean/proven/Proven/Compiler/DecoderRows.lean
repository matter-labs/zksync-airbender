module
public import Proven.Compiler.SetupMetadata
public import Proven.Trace.Machine.Program

@[expose] public section
namespace Airbender.Compiler.NativePublicSetup.Proofs
open Airbender Trace NativeArithmetic Metadata
set_option warningAsError true

/-- The final packed payload coordinate is the public selector mask. -/
theorem program_mask (family : RVMachineDecoderFamily) (entry : RVMachineProgramEntry)
    (matching : entry.data.family = family) :
    ((programRow family entry)[maskColumn family]?).getD 0 = (entry.data.mask : F) := by
  unfold programRow
  rw [ite_eq_left matching]
  unfold maskRow
  rw [columns_binding]
  cases family with
  | pooled family => cases family <;> kernel_rfl
  | unified => kernel_rfl

/-- Missing and unsupported decoder slots keep their complete minus-one payload. -/
theorem decoder_mask (family : RVMachineDecoderFamily) (program : List RVMachineProgramEntry)
    (index : Nat) :
    ((decoderRow family program index)[maskColumn family]?).getD 0 =
      match rvMachineProgramSlot program index with
      | some entry => if entry.data.family = family then (entry.data.mask : F) else -1
      | none => -1 := by
  unfold decoderRow
  cases slot : rvMachineProgramSlot program index with
  | none =>
    simp only [Option.map_none, Option.getD_none, width_binding]
    cases family with
    | pooled family => cases family <;> kernel_rfl
    | unified => kernel_rfl
  | some entry =>
    simp only [Option.map_some, Option.getD_some]
    by_cases matching : entry.data.family = family
    · rw [ite_eq_left matching]
      unfold programRow maskRow
      rw [ite_eq_left matching, columns_binding]
      cases family with
      | pooled family => cases family <;> kernel_rfl
      | unified => kernel_rfl
    · rw [ite_eq_right matching]
      unfold programRow
      rw [ite_eq_right matching, width_binding]
      cases family with
      | pooled family => cases family <;> kernel_rfl
      | unified => kernel_rfl

/-- The destination is retained by every native decoder mask. -/
theorem program_destination (family : RVMachineDecoderFamily) (entry : RVMachineProgramEntry)
    (matching : entry.data.family = family) :
    ((programRow family entry)[4]?).getD 0 = (entry.data.rd : F) := by
  unfold programRow
  rw [ite_eq_left matching]
  unfold maskRow
  rw [columns_binding]
  cases family with
  | pooled family => cases family <;> kernel_rfl
  | unified => kernel_rfl

/-- The destination coordinate keeps the native sentinel for absent or other-family entries. -/
theorem decoder_destination (family : RVMachineDecoderFamily) (program : List RVMachineProgramEntry)
    (index : Nat) :
    ((decoderRow family program index)[4]?).getD 0 =
      match rvMachineProgramSlot program index with
      | some entry => if entry.data.family = family then (entry.data.rd : F) else -1
      | none => -1 := by
  unfold decoderRow
  cases slot : rvMachineProgramSlot program index with
  | none =>
    simp only [Option.map_none, Option.getD_none, width_binding]
    cases family with
    | pooled family => cases family <;> kernel_rfl
    | unified => kernel_rfl
  | some entry =>
    simp only [Option.map_some, Option.getD_some]
    by_cases matching : entry.data.family = family
    · rw [ite_eq_left matching]
      unfold programRow maskRow
      rw [ite_eq_left matching, columns_binding]
      cases family with
      | pooled family => cases family <;> kernel_rfl
      | unified => kernel_rfl
    · rw [ite_eq_right matching]
      unfold programRow
      rw [ite_eq_right matching, width_binding]
      cases family with
      | pooled family => cases family <;> kernel_rfl
      | unified => kernel_rfl

private theorem cast_nonzero (value : Nat) (positive : 0 < value) (small : value < babyBearModulus) :
    (value : F) ≠ 0 := by
  intro zero
  have same := congrArg ZMod.val zero
  have valueZero : value = 0 := by
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt small, ZMod.val_zero] using same
  omega

/-- A decoder row has a nonzero mask, or a load-family row has a nonzero destination. -/
theorem decoder_row_nonzero {initial : RV.State} {program : List RVMachineProgramEntry}
    {actual : ProgramLookupRows} (bound : Bound initial program actual)
    (family : RVMachineDecoderFamily) (index : Nat) :
    ((decoderRow family program index)[maskColumn family]?).getD 0 ≠ 0 ∨
      ((family = .pooled .wordMemory ∨ family = .pooled .subwordMemory) ∧
        ((decoderRow family program index)[4]?).getD 0 ≠ 0) := by
  rw [decoder_mask, decoder_destination]
  cases slot : rvMachineProgramSlot program index with
  | none => exact Or.inl (neg_ne_zero.mpr one_ne_zero)
  | some entry =>
    dsimp only
    by_cases matching : entry.data.family = family
    · simp only [ite_eq_left matching]
      have member := Trace.Machine.Proofs.machine_program_slot_member slot
      rcases bound.mask entry member with positive | ⟨load, _, positive, small⟩
      · exact Or.inl (cast_nonzero _ positive.1 positive.2)
      · exact Or.inr ⟨by simpa only [matching] using load, cast_nonzero _ positive small⟩
    · rw [ite_eq_right matching]
      exact Or.inl (neg_ne_zero.mpr one_ne_zero)

/-- Tagged decoder slots retain discriminator 46, including unsupported slots. -/
theorem decoder_tag (family : RVMachineDecoderFamily) (isTagged : tagged family = true)
    (program : List RVMachineProgramEntry) (index : Nat) :
    ((decoderRow family program index)[width family - 1]?).getD 0 = 46 := by
  unfold decoderRow
  rw [width_binding]
  cases slot : rvMachineProgramSlot program index with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    cases family with
    | pooled family =>
      cases family with
      | addSub => simp [tagged] at isTagged
      | jumpBranchSlt => kernel_rfl
      | mulDiv => kernel_rfl
      | shiftBinop => kernel_rfl
      | wordMemory => kernel_rfl
      | subwordMemory => kernel_rfl
    | unified => kernel_rfl
  | some entry =>
    simp only [Option.map_some, Option.getD_some]
    unfold programRow
    rw [width_binding]
    by_cases matching : entry.data.family = family
    · rw [ite_eq_left matching]
      unfold maskRow
      rw [columns_binding]
      cases family with
      | pooled family =>
        cases family with
        | addSub => simp [tagged] at isTagged
        | jumpBranchSlt => kernel_rfl
        | mulDiv => kernel_rfl
        | shiftBinop => kernel_rfl
        | wordMemory => kernel_rfl
        | subwordMemory => kernel_rfl
      | unified => kernel_rfl
    · rw [ite_eq_right matching]
      cases family with
      | pooled family =>
        cases family with
        | addSub => simp [tagged] at isTagged
        | jumpBranchSlt => kernel_rfl
        | mulDiv => kernel_rfl
        | shiftBinop => kernel_rfl
        | wordMemory => kernel_rfl
        | subwordMemory => kernel_rfl
      | unified => kernel_rfl

end Airbender.Compiler.NativePublicSetup.Proofs
