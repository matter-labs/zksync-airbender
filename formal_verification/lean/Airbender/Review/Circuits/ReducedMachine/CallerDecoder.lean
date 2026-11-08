import Airbender.Review.Circuits.ReducedMachine.MainDecoder
import Airbender.Review.Circuits.ReducedMachine.UnifiedDecoder
import Airbender.Review.Circuits.ReducedMachine.CSRDecoder
import Airbender.Review.Circuits.ReducedMachine.RuntimeCSR

namespace Airbender.NativeCallerDecoder
open Airbender.ReducedMachine.Native Airbender.Trace
abbrev F := ZMod mersenne31Modulus

/-- Seven existing ordinary profiles and original CSRRW, without changing their
    projections or importing any CSR/MOP execution semantics. -/
abbrev Mode := Sum UnifiedMode CSRMode

def decoderFields (instruction : SailRV32.instruction) : Option (DecoderData Mode) :=
  match unifiedDecoderFields instruction with
  | some data => some (data.mapFamily Sum.inl)
  | none => (csrDecoderFields instruction).map (DecoderData.mapFamily Sum.inr)

abbrev Program := ProgramEntry Mode
abbrev setupImage := sparseDecoderSetupImageRunWith decoderFields

/-- Actual request conclusions for a valid fetched entry. Inactive physical rows
    are not asserted to have this shape. No issuance/matching or original CSR
    execution is inferred from these native observables. -/
structure RowEffects (w : Nat → F) (entry : Program) : Prop where
  boolean : (csrRequest w).multiplicity = 0 ∨ (csrRequest w).multiplicity = 1
  shape : csrRequest w = ⟨0,0,some 0,3⟩ ∨
    (∃ rs1 rd : BitVec 5,
      entry.instruction = .CSRReg (1991,.Regidx rs1,.Regidx rd,.CSRRW) ∧
      w 12 = (csrMask : F) ∧ (w 9).val = 1991 ∧
      csrRequest w = ⟨1,1991,some (w 36),3⟩ ∧ csrOracleWord w = ⟨0,0⟩ ∧ (w 93).val < 65536)

/-- Same actual counted main observations, selected ONLY by execute1. All
    ordinary inactive callers and their auxiliary values stay in SourceAccepted. -/
def Effects {R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Mode) (batch : Airbender.NativeMainDecoder.Batch R) : Prop :=
  ∀ proof ∈ batch.proofs, ∀ i < decoderAuxiliaryLayout.traceLength-1,
    proof.initialization.main.memory.rows i importedConstraintsTraceColumns.execute = 1 →
      ∃ entry ∈ publicSetup.program, entry.SourceWith before decoderFields ∧
        decoderQuery (proof.initialization.main.memory.rows i) = entry.query ∧
        RowEffects (proof.initialization.main.memory.rows i) entry
end Airbender.NativeCallerDecoder
