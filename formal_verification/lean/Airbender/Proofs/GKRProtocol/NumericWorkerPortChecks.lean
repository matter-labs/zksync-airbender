import Airbender.Proofs.GKRProtocol.NumericFunctionalBaseChecks
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings

namespace Airbender.Compiler.NumericWorkerPortChecks
set_option warningAsError true

structure Typed where
  columns : List (GKRAddress × GKRAddress)
  bounds : List (Nat × Nat)

def Typed.check (source : Typed) : Bool :=
  source.columns.all (fun row => decide (row.1 = row.2)) &&
  source.bounds.all (fun row => decide (row.1 < row.2))

structure Data where
  columns : List (Nat × Nat)
  bounds : List (Nat × Nat)

def encode (source : Typed) : Data where
  columns := source.columns.map fun row =>
    (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)
  bounds := source.bounds

def check (data : Data) : Bool :=
  data.columns.all (fun row => row.1 == row.2) &&
  data.bounds.all (fun row => decide (row.1 < row.2))

theorem addressCode_eq (left right : GKRAddress) :
    (AddressUniqueChecks.addressCode left == AddressUniqueChecks.addressCode right) =
      decide (left = right) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq]
  exact CleanPlacementChecks.addressCode_injective.eq_iff

theorem encode_check (source : Typed) : check (encode source) = source.check := by
  simp only [check, encode, Typed.check, List.all_map, Function.comp_def, addressCode_eq]

theorem check_sound (source : Typed) (data : Data)
    (binding : data = encode source) (checked : check data = true) : source.check = true := by
  rw [binding, encode_check] at checked
  exact checked

theorem merge_at (values referenceValues : List α) (first left right next partCount : Nat)
    (next_eq : next = first + left) (partCount_eq : partCount = left + right)
    (firstBinding : (values.drop first).take left = (referenceValues.drop first).take left)
    (secondBinding : (values.drop next).take right = (referenceValues.drop next).take right) :
    (values.drop first).take partCount = (referenceValues.drop first).take partCount := by
  subst next; subst partCount
  exact NumericQueryFrameChecks.merge_bindings values referenceValues first left right firstBinding secondBinding

end Airbender.Compiler.NumericWorkerPortChecks
