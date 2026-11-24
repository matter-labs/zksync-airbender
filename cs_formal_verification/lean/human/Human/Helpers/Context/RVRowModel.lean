module
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.Helpers.Core.BabyBearPrime
public import Human.ISA.RV32

@[expose] public section

/-! Shared row interpretation for ADD/SUB, MUL/DIV, shifts and bit operations, word and subword memory,
    and jump, branch and comparison circuits. `RVRowMapping` binds the imported words, the state at the
    row clock, and the decoded public instruction. `rvRowModel` requires an accepted trace, program
    decoding and row membership. Each family claim adds its public interface assumptions and states
    its result for our RV32 spec (`RV.step`). -/

namespace Airbender.Trace

/-- How an RV row claim reads one row of `family`: `words` ties the input and output to the imported variables, the
    row's pre-state `before input` is the RV state at its clock position (`RVRowPosition`), and its decoder query
    matches a public program entry of `family` whose encoding decodes to `instruction input`. -/
structure RVRowMapping {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) (input : Input) (output : Output) (w : Nat → ZMod babyBearModulus) :
    Prop where
  /-- Bind the input and output words to the imported witness columns. -/
  words : words input output w
  /-- Bind the pre-state to the row position in the initialized history. -/
  state : RVRowPosition trace initial cells ⟨family, w⟩ (before input)
  /-- Bind the row decoder query to a public entry for the selected instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = family ∧ (⟨family, w⟩ : Row babyBearModulus PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (instruction input)

/-- An RV row family's per-row model: a row of `family` in an accepted, decoded trace, read by `RVRowMapping`. -/
def rvRowModel {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) : Verification.CircuitModel Input Output (Nat → ZMod babyBearModulus) where
  satisfies := fun w => Accepted trace ∧ RVPooledDecoded trace program ∧
    (⟨family, w⟩ : Row babyBearModulus PooledFamily) ∈ trace.rows
  represents := RVRowMapping (family := family) (before := before) (instruction := instruction)
    (words := words) trace initial cells program

/-- The assumptions of a per-row RV claim can be met (lean-strategies 3.3): some public setup meeting `assumptions`
    has a row of `family` that the model relates to some input and output. -/
def RVRowSatisfiable {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (assumptions : PooledTrace babyBearModulus → RV.State → List Cell → List RVPooledProgramEntry → Prop) : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) (input : Input) (output : Output) (w : Nat → ZMod babyBearModulus),
    assumptions trace initial cells program ∧
      (rvRowModel (family := family) (before := before) (instruction := instruction)
        (words := words) trace initial cells program).relation input output w


end Airbender.Trace
