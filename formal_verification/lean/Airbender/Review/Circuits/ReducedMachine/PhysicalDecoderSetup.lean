import Airbender.Review.Circuits.ReducedMachine.DecoderTableArguments
import Airbender.Review.Helpers.Decoder.StatefulSetup
import Airbender.Review.Helpers.Tables.NormalizeLast

namespace Airbender.ReducedMachine.NativePhysicalDecoderSetup
open Native Trace NativeDecoderTableArguments
abbrev F := ZMod mersenne31Modulus

/-- Exact indexed public slice: holes and its whole configured tail remain. -/
def sliceSize {Kind : Type} (setup : SparseDecoderSetup Kind) : Nat := setup.slots.length+setup.padding

/-- get_main_domain_trace copies the input slice, then actual minus-one padding
    through EVERY remaining ordinary physical row. No ROM image is identified. -/
def ordinaryRow {Kind : Type} (setup : SparseDecoderSetup Kind) (i : Nat) : Vector F 10 :=
  if bound : i < sliceSize setup then setup.row ⟨i,bound⟩ else Vector.replicate 10 (-1)

/-- The normalized final row is a negative column sum, not a lookup row. -/
def normalizedRow {Kind : Type} (setup : SparseDecoderSetup Kind) (i : Nat) : Vector F 10 :=
  Verification.normalizeRows decoderTableLayout.traceLength (ordinaryRow setup) i

/-- Construct physical decoder columns6..15 from the public slice and native
    row normalization. Other observed setup columns are retained. This is an
    explicit source-reference construction, NOT physical commitment/Rust/FFT or
    public-ROM authentication, nor equality to an arbitrary observed table. -/
def withPublicSetup {Kind R : Type} [Field R] (setup : SparseDecoderSetup Kind) (proof : Proof R) : Proof R :=
  { proof with setup := fun i column =>
      if inDecoder : decoderTableLayout.setupStart ≤ column.index ∧
          column.index < decoderTableLayout.setupStart+10 then
        (normalizedRow setup i)[(⟨column.index-decoderTableLayout.setupStart,by omega⟩ : Fin 10)]
      else proof.setup i column }

/-- Actual ordinary physical decoder rows only; the normalization row is never
    supplied as a lookup. Membership/extraction remains an explicit boundary. -/
def table {Kind : Type} (setup : SparseDecoderSetup Kind) : Table F (fields 10) := .fromStatic {
  name := "Airbender.V2PhysicalDecoderOrdinary"
  length := decoderTableLayout.traceLength-1
  row := fun i => ordinaryRow setup i.val
  index query := setup.slots.toArray.findIdx fun slot =>
    match slot with
    | some entry => entry.query == query
    | none => Vector.replicate 10 (-1) == query
  Spec query := ∃ i : Fin (decoderTableLayout.traceLength-1), query = ordinaryRow setup i.val
  contains_iff _ := Iff.rfl
}
end Airbender.ReducedMachine.NativePhysicalDecoderSetup
