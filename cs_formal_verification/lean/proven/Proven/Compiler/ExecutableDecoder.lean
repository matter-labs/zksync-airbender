module
public import Proven.Compiler.SetupMetadata

@[expose] public section
namespace Airbender.Compiler.NativePublicSetup
open Airbender Trace Arithmetic NativeArithmetic Metadata
set_option warningAsError true

/-- The executable payload uses the mask whose equality to the native circuit is kernel checked. -/
def programRowNat (family : RVMachineDecoderFamily) (entry : RVMachineProgramEntry) : List Nat :=
  if entry.data.family = family then
    (entry.data.row entry.pc).toList.zipIdx.filterMap fun (value, index) =>
      if (columns family)[index]?.getD false then some value else none
  else List.replicate (width family - if tagged family then 1 else 0) (babyBearModulus - 1)

/-- The executable decoder row retains the public PC index and native sentinels. -/
def decoderRowNatWith (family : RVMachineDecoderFamily)
    (slot : Nat → Option RVMachineProgramEntry) (index : Nat) : List Nat :=
  let payload := (slot index).map (programRowNat family) |>.getD
    (List.replicate (width family - if tagged family then 1 else 0) (babyBearModulus - 1))
  if tagged family then payload ++ [46] else payload

/-- The executable payload is the payload in the public native setup definition. -/
theorem programRowNat_binding (family : RVMachineDecoderFamily) (entry : RVMachineProgramEntry) :
    (programRowNat family entry).map (fun (value : Nat) => (value : F)) = programRow family entry := by
  unfold programRowNat programRow
  rw [width_binding]
  by_cases matching : entry.data.family = family
  · rw [ite_eq_left matching, ite_eq_left matching]
    unfold maskRow
    rw [columns_binding]
    cases family with
    | pooled family => cases family <;> kernel_rfl
    | unified => kernel_rfl
  · rw [ite_eq_right matching, ite_eq_right matching]
    cases family with
    | pooled family => cases family <;> kernel_rfl
    | unified => kernel_rfl

/-- The executable row equals the decoder row used by the machine target. -/
theorem decoderRowNat_binding (family : RVMachineDecoderFamily)
    (program : List RVMachineProgramEntry) (index : Nat) :
    (decoderRowNatWith family (rvMachineProgramSlot program) index).map (fun (value : Nat) => (value : F)) =
      decoderRow family program index := by
  unfold decoderRowNatWith decoderRow
  rw [width_binding]
  cases slot : rvMachineProgramSlot program index with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    cases family with
    | pooled family => cases family <;> kernel_rfl
    | unified => kernel_rfl
  | some entry =>
    simp only [Option.map_some, Option.getD_some]
    cases tagged family with
    | false => exact programRowNat_binding family entry
    | true =>
      change (programRowNat family entry ++ [46]).map (fun (value : Nat) => (value : F)) =
        programRow family entry ++ [46]
      rw [List.map_append, programRowNat_binding]
      rfl

/-- At a decoder address, the full public setup uses the executable decoder row. -/
theorem rows_decoder_binding (initial : RV.State) (family : RVMachineDecoderFamily)
    (program : List RVMachineProgramEntry) (index : NativeSetupIndex family)
    (inside : index.val - offset family < decoderCapacity)
    (afterFixed : offset family ≤ index.val) :
    rows initial program family 0 index =
      (decoderRowNatWith family (rvMachineProgramSlot program) (index.val - offset family)).map
        (fun (value : Nat) => (value : F)) := by
  simp only [rows, Fin.val_zero, ↓reduceIte, genericRow, offset_binding,
    Nat.not_lt.mpr afterFixed, inside]
  exact (decoderRowNat_binding family program _).symm

end Airbender.Compiler.NativePublicSetup
