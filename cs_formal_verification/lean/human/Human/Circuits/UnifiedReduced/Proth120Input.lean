module
public import Human.Circuits.UnifiedReduced.Proth120Execution

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace

/-- The public ROM encodes a read or write of CSR 0x7c0. A read selects bit eight and writes
    its response to the decoded register. A write has the native NOP metadata. -/
def CSRDecoded (before : RV.State) (query : Vector (ZMod proth120Modulus) 9) (read : Bool) : Prop :=
  ∃ r : RV.Reg, r ≠ 0 ∧ RV.decode (RV.read before.rom before.pc 4) =
    some (if read then .inputRead r else .inputWrite r) ∧ query =
    (⟨before.pc, RV.read before.rom before.pc 4,
      if read then ⟨.machine, 0, 0, r, ⟨0, 0⟩, 256, 0⟩ else rvNopFields⟩ : RVProgramEntry).query

/-- The input word belongs to the independent stream in the pre-state. -/
def CSRResponse (w : Nat → ZMod proth120Modulus) (before : RV.State) (read : Bool) : Prop :=
  read = true → before.input.head? = some (wordAt w 50).toBitVec

structure CSRInputs (cells : List Cell) (epoch : Nat) (w : Nat → ZMod proth120Modulus)
    (before after : RV.State) (read : Bool) : Prop extends RowContext cells epoch w before after where
  constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (tableWith (ROM.wordsRV before)))
  decoded : CSRDecoded before (nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w) read
  response : CSRResponse w before read

def CSRRowSoundnessClaim : Prop := ∀ cells epoch w before after read, CSRInputs cells epoch w before after read →
  StepResult w before { after with input := before.input.drop read.toNat }

def CSRRowSoundnessSatisfiableClaim : Prop := ∃ cells epoch w before after read,
  CSRInputs cells epoch w before after read ∧ read = true ∧ before.input = [7, 11]

end Airbender.UnifiedReduced.Proth120
