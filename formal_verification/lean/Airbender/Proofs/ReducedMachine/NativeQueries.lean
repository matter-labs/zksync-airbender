import Airbender.Review.Circuits.ReducedMachine.NativeArtifact
import Airbender.Review.Circuits.ReducedMachine.Tables.NativeTheorems
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties

namespace Airbender.ReducedMachine.NativeQueryProofs
open Verification
set_option warningAsError true
set_option Elab.async false

/-- Extract the two actual constant queries from original Clean acceptance. -/
theorem queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (Native.importedConstraints NativeFixed.table)) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 36,w 56,w 57,16] ∧
      (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 48,w 59,w 60,16] := by
  constructor
  · have query := lookup_of_holds holds ⟨16,by change 16 < 22; decide⟩
    simpa [Native.importedConstraints,FlatOperation.lookups,Lookup.Contains,
      Table.toRaw,NativeFixed.table,Table.fromStatic,StaticTable.toTable,
      Expression.eval,environment,ProvableType.fromElements] using query
  · have query := lookup_of_holds holds ⟨17,by change 17 < 22; decide⟩
    simpa [Native.importedConstraints,FlatOperation.lookups,Lookup.Contains,
      Table.toRaw,NativeFixed.table,Table.fromStatic,StaticTable.toTable,
      Expression.eval,environment,ProvableType.fromElements] using query

theorem results {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (Native.importedConstraints NativeFixed.table)) :
    (w 36).val < 65536 ∧ (w 56).val = (w 36).val / 32768 ∧
      (w 57).val = (w 36).val / 256 ∧
    (w 48).val < 65536 ∧ (w 59).val = (w 48).val / 32768 ∧
      (w 60).val = (w 48).val / 256 := by
  obtain ⟨first,second⟩ := queries holds
  have a := NativeFixed.sign_high _ first rfl
  have b := NativeFixed.sign_high _ second rfl
  exact ⟨a.1,a.2.1,a.2.2.1,b.1,b.2.1,b.2.2.1⟩

end Airbender.ReducedMachine.NativeQueryProofs
