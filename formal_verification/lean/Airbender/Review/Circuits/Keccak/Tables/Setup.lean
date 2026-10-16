import Airbender.Review.Circuits.Keccak.Tables.ControllerData
import Airbender.Review.Circuits.Keccak.Tables.FixedData
import Airbender.Review.Circuits.Keccak.Tables.Operations
import Airbender.Review.Circuits.Keccak.Artifact
import Airbender.Review.Helpers.Properties

namespace Airbender.Keccak

/- Fixed rows are native artifact data. The generalized controller interface
   retains its arbitrary outputs; the concrete native controller is imported. -/
def setupRow (control : Fin 4096 → Vector Nat 6) (index : Fin 1249281) : Vector Nat 8 :=
  let n := index.val
  if n = zeroDataRegion.offset then fixedRow 0 (n - zeroDataRegion.offset)
  else if n < xorDataRegion.offset + xorDataRegion.length then
    fixedRow 1 (n - xorDataRegion.offset)
  else if h : n < controllerDataRegion.offset + controllerDataRegion.length then
    let key : Fin 4096 := ⟨n - controllerDataRegion.offset, by
      have bound := index.isLt
      dsimp only [controllerDataRegion, zeroDataRegion, xorDataRegion] at *
      omega⟩
    let outputs := control key
    #v[key.val, outputs[0], outputs[1], outputs[2], outputs[3], outputs[4], outputs[5], 37]
  else if n < iotaDataRegion.offset + iotaDataRegion.length then
    fixedRow 2 (n - iotaDataRegion.offset)
  else if n < chiDataRegion.offset + chiDataRegion.length then
    fixedRow 3 (n - chiDataRegion.offset)
  else fixedRow 4 (n - rotationDataRegion.offset)

def setupTable {p : Nat} [Fact p.Prime] (control : Fin 4096 → Vector Nat 6) :
    Table (ZMod p) (fields 8) := .fromStatic {
  name := "Airbender.Keccak"
  length := 1249281
  row i := (setupRow control i).map (fun (n : Nat) => (n : ZMod p))
  index x := match x[7].val with
    | 4 => xorDataRegion.offset + 256 * x[0].val + x[1].val
    | 37 => controllerDataRegion.offset + x[0].val
    | 38 => iotaDataRegion.offset + x[0].val + 256 * x[1].val
    | 39 => chiDataRegion.offset + x[0].val + 256 * x[1].val
    | 40 => rotationDataRegion.offset + x[0].val
    | _ => zeroDataRegion.offset
  Spec x := ∃ i : Fin 1249281, x = (setupRow control i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}
/-- Every native byte query has bounded, exact outputs, including padding.
    The fixed table contents are imported native data. -/
def ByteLookupChecks {p : Nat} [Fact p.Prime]
    (control : Fin 4096 → Vector Nat 6) (w : Nat → ZMod p) : Prop :=
  ∀ i : Fin 40,
    let entry := ((FlatOperation.lookups (importedConstraints (setupTable control))).get
      ⟨i.val + 2, by rw [lookup_count]; omega⟩).entry.toArray
    let value := fun j => (entry[j]!.eval (Verification.environment w)).val
    ByteOperationFacts (value 7) (value 0) (value 1) (value 2)

end Airbender.Keccak

