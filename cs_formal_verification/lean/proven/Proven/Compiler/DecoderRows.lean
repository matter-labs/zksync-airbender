module
public import Proven.Compiler.SetupMetadata

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
      match program[index]? with
      | some entry => if entry.data.family = family then (entry.data.mask : F) else -1
      | none => -1 := by
  unfold decoderRow
  cases slot : program[index]? with
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

/-- Every supported public entry and every sentinel has a nonzero selector mask. -/
theorem decoder_mask_nonzero {initial : RV.State} {program : List RVMachineProgramEntry}
    {actual : ProgramLookupRows} (bound : Bound initial program actual)
    (family : RVMachineDecoderFamily) (index : Nat) :
    ((decoderRow family program index)[maskColumn family]?).getD 0 ≠ 0 := by
  rw [decoder_mask]
  cases slot : program[index]? with
  | none => exact neg_ne_zero.mpr one_ne_zero
  | some entry =>
    dsimp only
    by_cases matching : entry.data.family = family
    · rw [ite_eq_left matching]
      have member : entry ∈ program := by
        obtain ⟨present, rfl⟩ := List.getElem?_eq_some_iff.mp slot
        exact List.getElem_mem present
      have mask := bound.mask entry member
      intro zero
      have value := congrArg ZMod.val zero
      have zeroNat : entry.data.mask = 0 := by
        simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt mask.2, ZMod.val_zero] using value
      exact (Nat.ne_of_gt mask.1) zeroNat
    · rw [ite_eq_right matching]
      exact neg_ne_zero.mpr one_ne_zero

/-- Tagged decoder slots retain discriminator 46, including unsupported slots. -/
theorem decoder_tag (family : RVMachineDecoderFamily) (isTagged : tagged family = true)
    (program : List RVMachineProgramEntry) (index : Nat) :
    ((decoderRow family program index)[width family - 1]?).getD 0 = 46 := by
  unfold decoderRow
  rw [width_binding]
  cases slot : program[index]? with
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
