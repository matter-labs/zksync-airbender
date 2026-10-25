import GKRProtocol.CleanClosedNative.WordMemoryUncached
import GKRProtocol.DecoderQueryNative.WordMemoryUncached
import GKRProtocol.FramedWitnessNative.WordMemoryUncached
import GKRProtocol.PublicConstraints
import GKRProtocol.ROMNative.WordFullPublic
import GKRProtocol.ROMNative.SubwordPublic
import Airbender.Review.Helpers.Decoder.PooledProgram

namespace Airbender.Compiler.PooledRowNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The same canonical source frame and actual native arithmetic relation used
by the complete compiler-witness theorem. Logical lookup validity is explicit. -/
structure Certificate where
  sourceValue : Fin Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputs.length → Source.BaseField
  counts : Fin Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.length → Source.BaseField
  physical : GKRAddress → Source.BaseField
  frame : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address wire) =
    Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native.canonical sourceValue) counts wire
  arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0
  helpers : ∀ field ∈ Airbender.Compiler.HelperNative.WordMemoryUncached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.WordMemoryUncached.native.sourceValues physical)).val < 524288
  authored : Airbender.Compiler.MaterializedWitnessNative.WordMemoryUncached.AuthoredLookupValid sourceValue
  active : (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.WordMemory.importedConstraintsTraceColumns.execute = 1

/-- A complete native graph witness supplies the arithmetic, canonical frame
and helper range fields of the execution cert without additional claims. -/
def ofWitness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputs.length → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (index : Fin Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.imported.data.length)
    (fallback physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (native : Airbender.Compiler.FramedWitnessNative.WordMemoryUncached.CompleteRowWitness hom challenges gamma sourceValue counts index fallback physical values)
    (authored : Airbender.Compiler.MaterializedWitnessNative.WordMemoryUncached.AuthoredLookupValid sourceValue)
    (active : (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment physical (fun _ _ => #[])).get
      Airbender.WordMemory.importedConstraintsTraceColumns.execute = 1) : Certificate := by
  rcases native.1 with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩
  exact ⟨sourceValue, counts, physical, inputsAt, arithmetic, helpers, authored, active⟩

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.wordMemory, (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment cert.physical (fun _ _ => #[])).get⟩

theorem active (cert : Certificate) :
    (row cert).assignment (row cert).columns.execute = 1 := cert.active

theorem constraints (cert : Certificate) {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (physical : Trace.initialImage before cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row cert).assignment)
      ((row cert).constraints (⟨Trace.ROM.table cells tokens,
        Verification.subwordTable (Trace.ROM.words before)⟩ : Trace.PooledSetup babyBearModulus)) := by
  have native := Airbender.Compiler.CleanClosedNative.WordMemoryUncached.retained_clock_from_source cert.sourceValue cert.counts
    cert.physical (fun _ _ => #[]) cert.frame cert.arithmetic cert.helpers cert.authored
  exact PublicConstraints.word_transport _ _ _ native
    (fun _ member guard => ROMNative.WordFullPublic.public_refinement image physical domain member guard)

theorem decoded (cert : Certificate)
    (typed : (row cert).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.pooledProgram (row cert).family).Contains #[]
      (row cert).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.WordMemoryUncached.program_from_framed_source (by decide +kernel)
    cert.sourceValue cert.counts cert.physical (fun _ _ => #[])
    cert.frame cert.arithmetic typed ?_ cert.authored
  have enabled := cert.active
  simpa [Airbender.Compiler.DecoderArgumentsNative.WordMemoryUncached.native.expression0, _root_.Expression.eval] using
    (show ((Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment cert.physical (fun _ _ => #[])).get
      Airbender.WordMemory.importedConstraintsTraceColumns.execute) ≠ 0 by rw [enabled]; exact one_ne_zero)

end Airbender.Compiler.PooledRowNative.WordMemoryUncached
