module
public import Human.Compiler.NativePublicSetup

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativePublicSetup.Proofs
open Airbender Trace NativeArithmetic

/-- Complete native virtual rows contain only values below their increasing-prefix limit. -/
theorem scalar_bound (limit : Nat) (positive : 0 < limit) (index : Nat) (value : F)
    (same : [value] = [if index < limit then (index : F) else 0]) : value.val < limit := by
  have scalar := List.singleton_inj.mp same
  by_cases bounded : index < limit
  · rw [ite_eq_left bounded] at scalar
    rw [scalar, ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) bounded
  · rw [ite_eq_right bounded] at scalar
    simpa only [scalar, ZMod.val_zero] using positive

/-- Native exact lookup membership into group one proves the 16-bit range. -/
theorem range16_bound {initial : RV.State} {program : List RVMachineProgramEntry}
    {family : RVMachineDecoderFamily} {index : NativeSetupIndex family} {value : F}
    (same : [value] = rows initial program family 1 index) : value.val < 65536 := by
  apply scalar_bound 65536 (by decide) index.val value
  exact same

/-- Native exact lookup membership into group two proves the 19-bit helper range. -/
theorem timestamp_bound {initial : RV.State} {program : List RVMachineProgramEntry}
    {family : RVMachineDecoderFamily} {index : NativeSetupIndex family} {value : F}
    (same : [value] = rows initial program family 2 index) : value.val < 524288 := by
  apply scalar_bound 524288 (by decide) index.val value
  exact same

/-- Membership refers to independently interpreted finite native setup rows. -/
def Contains (initial : RV.State) (program : List RVMachineProgramEntry)
    (family : RVMachineDecoderFamily) (group : Fin 3) (fields : List F) : Prop :=
  ∃ index : NativeSetupIndex family, fields = rows initial program family group index

/-- Native range membership has the retained Clean table meaning. -/
theorem range16_clean_refinement {initial : RV.State} {program : List RVMachineProgramEntry}
    {family : RVMachineDecoderFamily} (value : F)
    (member : Contains initial program family 1 [value]) (provided : Array F) :
    (Verification.range16Table (p := babyBearModulus)).Contains provided value := by
  obtain ⟨index, same⟩ := member
  have bounded := range16_bound same
  change ∃ index : Fin 65536, value = (index.val : F)
  exact ⟨⟨value.val, bounded⟩, (ZMod.natCast_zmod_val value).symm⟩

end Airbender.Compiler.NativePublicSetup.Proofs
