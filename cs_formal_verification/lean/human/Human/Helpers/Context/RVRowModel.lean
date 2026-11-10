module
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.Helpers.Core.BabyBearPrime
public import Human.ISA.RV32

@[expose] public section

/-! The shape shared by the per-row RV claims of the pooled families (AddSub, MulDiv, ShiftBinop, SubwordMemory,
    WordMemory, JumpBranchSlt): what a row of a family is, read in RV32 terms, and what the claim asserts about it.
    Each family supplies its input type, `before` (the row's pre-state), its instruction, its word mapping (the
    imported variable IDs), its public assumptions and its conclusion. -/

namespace Airbender.Trace

/-- How an RV row claim reads one row of `family`: `words` ties the input and output to the imported variables, the
    row's pre-state `before input` is the RV state at its clock position (`RVRowPosition`), and its decoder query
    matches a public program entry of `family` whose encoding decodes to `instruction input`. -/
structure RVRowMapping {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) (input : Input) (output : Output) (w : Nat → ZMod babyBearModulus) :
    Prop where
  words : words input output w
  state : RVRowPosition trace initial cells ⟨family, w⟩ (before input)
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
  represents := RVRowMapping family before instruction words trace initial cells program

/-- The shape of the per-row RV claims: for every public setup meeting `assumptions`, every row the model relates
    satisfies `conclusion`. -/
def RVRowSoundness {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (assumptions : PooledTrace babyBearModulus → RV.State → List Cell → List RVPooledProgramEntry → Prop)
    (conclusion : Input → Output → Prop) : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    assumptions trace initial cells program →
    ∀ input output w, (rvRowModel family before instruction words trace initial cells program).relation input output w →
      conclusion input output

end Airbender.Trace
