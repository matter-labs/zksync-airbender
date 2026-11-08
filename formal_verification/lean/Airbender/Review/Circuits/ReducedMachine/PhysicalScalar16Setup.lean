import Airbender.Review.Circuits.ReducedMachine.Scalar16Arguments
import Airbender.Review.Helpers.Tables.NativeScalarData
import Airbender.Review.Helpers.Tables.NormalizeLast

namespace Airbender.NativePhysicalScalar16Setup
open Airbender.ReducedMachine.Native Airbender.NativeScalar16Arguments

/-- Native scalar setup0 copies the actual exported prefix into a zeroed trace.
    Every ordinary tail row remains. The selected reduced domain is 2^23. -/
def ordinaryValue (i : Nat) : F :=
  if bound : i < Verification.NativeSetup.ScalarKind.range16.data.length then
    (Verification.NativeSetup.ScalarKind.range16.data.row ⟨i,bound⟩)[0] else 0

def ordinaryRow (i : Nat) : Vector F 1 := #v[ordinaryValue i]

/-- Closed value of native negative-column-sum normalization. Proofs derive
    32767 from the actual affine prefix and zero tail before using this value;
    it is not an assumed equality or an ordinary lookup row. -/
def normalizedValue (i : Nat) : F :=
  if i = scalar16Layout.traceLength-1 then 32767 else ordinaryValue i

def normalizedRow (i : Nat) : Vector F 1 := #v[normalizedValue i]

/-- Construct ONLY physical setup0 on the same proof. All other observed
    setup columns, witness/base/body/auxiliary data and claims are retained.
    This constructs public fixed input, not Rust/codec/LDE/commitment refinement. -/
def withPublicSetup {R : Type} [Field R] (proof : Proof R) : Proof R :=
  { proof with setup := fun i column =>
      if column.index = scalar16Layout.setup.index then normalizedValue i else proof.setup i column }

/-- Actual full ordinary scalar16 table, including every zero tail row and
    excluding the reserved normalization row. No table equivalence is assumed. -/
def table : Table F (fields 1) := .fromStatic {
  name := "Airbender.V2ReducedScalar16Ordinary"
  length := scalar16Layout.traceLength-1
  row := fun i => #v[ordinaryValue i.val]
  index query := query[0].val
  Spec query := ∃ i : Fin (scalar16Layout.traceLength-1), query = #v[ordinaryValue i.val]
  contains_iff _ := Iff.rfl
}
end Airbender.NativePhysicalScalar16Setup
