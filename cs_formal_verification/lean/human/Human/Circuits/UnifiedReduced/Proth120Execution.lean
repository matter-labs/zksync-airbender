module
public import Human.Circuits.UnifiedReduced.Tables.Proth120
public import Human.Circuits.UnifiedReduced.Proth120Modular
public import Human.Helpers.UnifiedReduced.RVProgram
public import Human.Helpers.UnifiedReduced.MemoryMap
public import Human.Helpers.Memory.RVHistory

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Arithmetic

def romEnd : Nat := 2^19
abbrev writable := RV.writableAt romEnd
abbrev loadView (s : RV.State) := s.loadViewAt romEnd
abbrev exec := RV.execAt romEnd
abbrev step := RV.stepAt romEnd

def decoderFields (i : RV.Instr) : Option (DecoderData UnifiedFamily) :=
  rvDecoderFields i <|> (do
    let .mop o rd rs1 rs2 := i | none
    let mask ← match o with
      | .add => some 8 | .sub => some 16 | .mul => some 32 | .fma => some 64 | .triAdd => none
    pure ⟨.machine, rs1, rs2, rd, ⟨0,0⟩, mask, 0⟩)

/-- Membership in the public decoder table at the PC of the RV pre-state. -/
def Decoded (before : RV.State) (query : Vector (ZMod proth120Modulus) 9) : Prop :=
  ∃ i data, RV.decode (RV.read before.rom before.pc 4) = some i ∧ decoderFields i = some data ∧
    query = (⟨before.pc, RV.read before.rom before.pc 4, data⟩ : RVProgramEntry).query

/-- Memory history supplies the three native reads and writes. The operand bounds are the
    interface to the initialized RAM argument. -/
structure RowContext (cells : List Cell) (epoch : Nat) (w : Nat → ZMod proth120Modulus)
    (before after : RV.State) : Prop where
  active : w importedConstraintsTraceColumns.execute = 1
  fetch : before.pc.toNat % 4 = 0 ∧ before.pc.toNat + 4 ≤ romEnd
  bounded : (wordAt w 36).Bounded ∧ (wordAt w 42).Bounded ∧ (wordAt w 48).Bounded
  aligned : ∀ c ∈ cells, c.Aligned
  history : RVHistory cells (importedConstraintsMemoryPorts.toList.map (fun port =>
    ((epoch + ((decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + port.clock.offset),
      port.address.code w, port.readCode w, port.writeCode w) : MemoryAccess))).reverse before after

structure RowInputs (cells : List Cell) (epoch : Nat) (w : Nat → ZMod proth120Modulus)
    (before after : RV.State) : Prop extends RowContext cells epoch w before after where
  constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints (tableWith (ROM.wordsRV before)))
  decoded : Decoded before (nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w)

def StepResult (w : Nat → ZMod proth120Modulus) (before after : RV.State) : Prop :=
  ∃ next, step before = some next ∧ RV.Same next
    { after with pc := (Word.mk (w importedConstraintsTraceColumns.finalPC[0]).val
      (w importedConstraintsTraceColumns.finalPC[1]).val).toBitVec }

def RowSoundnessClaim : Prop := ∀ cells epoch w before after, RowInputs cells epoch w before after → StepResult w before after

def RowSoundnessSatisfiableClaim : Prop := ∃ cells epoch w before after, RowInputs cells epoch w before after

end Airbender.UnifiedReduced.Proth120
