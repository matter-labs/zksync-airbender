import GKRProtocol.CleanClosedNative.SubwordMemoryUncached
import GKRProtocol.DecoderQueryNative.SubwordMemoryUncached
import GKRProtocol.FramedWitnessNative.SubwordMemoryUncached
import GKRProtocol.PublicConstraints
import GKRProtocol.ROMNative.WordFullPublic
import GKRProtocol.ROMNative.SubwordPublic
import Airbender.Review.Helpers.Decoder.PooledProgram

namespace Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The same canonical source frame and actual native arithmetic relation used
by the complete compiler-witness theorem. Logical lookup validity is explicit. -/
structure Certificate where
  sourceValue : Fin Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputs.length → Source.BaseField
  counts : Fin Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns.length → Source.BaseField
  physical : GKRAddress → Source.BaseField
  frame : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address wire) =
    Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.canonical sourceValue) counts wire
  arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0
  helpers : ∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields,
    (field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues physical)).val < 524288
  authored : Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.AuthoredLookupValid sourceValue
  active : (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical (fun _ _ => #[])).get
    Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1

/-- A complete native graph witness supplies the arithmetic, canonical frame
and helper range fields of the execution cert without additional claims. -/
def ofWitness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputs.length → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (index : Fin Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.imported.data.length)
    (fallback physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (native : Airbender.Compiler.FramedWitnessNative.SubwordMemoryUncached.CompleteRowWitness hom challenges gamma sourceValue counts index fallback physical values)
    (authored : Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.AuthoredLookupValid sourceValue)
    (active : (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical (fun _ _ => #[])).get
      Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1) : Certificate := by
  rcases native.1 with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩
  exact ⟨sourceValue, counts, physical, inputsAt, arithmetic, helpers, authored, active⟩

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.subwordMemory, (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment cert.physical (fun _ _ => #[])).get⟩

theorem active (cert : Certificate) :
    (row cert).assignment (row cert).columns.execute = 1 := cert.active

theorem constraints (cert : Certificate) {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (_physical : Trace.initialImage before cells = some tokens)
    (_domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row cert).assignment)
      ((row cert).constraints (⟨Trace.ROM.table cells tokens,
        Verification.subwordTable (Trace.ROM.words before)⟩ : Trace.PooledSetup babyBearModulus)) := by
  have native := Airbender.Compiler.CleanClosedNative.SubwordMemoryUncached.retained_clock_from_source cert.sourceValue cert.counts
    cert.physical (fun _ _ => #[]) cert.frame cert.arithmetic cert.helpers cert.authored
  exact PublicConstraints.subword_transport _ _ _ native
    (fun _ member guard => ROMNative.SubwordPublic.public_table_refinement image member guard)

theorem decoded (cert : Certificate)
    (typed : (row cert).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.pooledProgram (row cert).family).Contains #[]
      (row cert).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.SubwordMemoryUncached.program_from_framed_source (by decide +kernel)
    cert.sourceValue cert.counts cert.physical (fun _ _ => #[])
    cert.frame cert.arithmetic typed ?_ cert.authored
  have enabled := cert.active
  simpa [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression0, _root_.Expression.eval] using
    (show ((Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment cert.physical (fun _ _ => #[])).get
      Airbender.SubwordMemory.importedConstraintsTraceColumns.execute) ≠ 0 by rw [enabled]; exact one_ne_zero)

end Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
