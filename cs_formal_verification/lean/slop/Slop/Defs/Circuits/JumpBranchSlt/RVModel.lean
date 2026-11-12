module
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.Helpers.Core.CircuitOutput
public import Human.ISA.RV32
public import Human.Circuits.JumpBranchSlt.RVModel

/-! The per-family RV trace mapping and model, stated before the shared `Trace.RVRowMapping`/`Trace.rvRowModel`
(`Human/Helpers/Context/RVRowModel.lean`); the proofs still use them. Moved from `human/Human/Circuits/JumpBranchSlt/RVModel.lean`. -/

@[expose] public section

namespace Airbender.JumpBranchSlt.Comparison
open Arithmetic Variables Trace

/-- Trace mapping in RV32 terms: the row's pre-state is the RV state at its clock position, and its decoder entry in
    the public program is `RV.decode` of the entry's encoding, equal to the input's instruction. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Name the imported operand, register, destination and PC variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.jumpBranchSlt, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .jumpBranchSlt ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- The comparison's per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Circuit.Output (Nat → ZMod p) where
  satisfies := fun w =>
    Accepted trace ∧ RVPooledDecoded trace program ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- Assumptions of the RV statements: `RVTraceInputs`. No code-alignment premise is needed. -/
abbrev RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  RVTraceInputs trace initial cells program

end Airbender.JumpBranchSlt.Comparison

namespace Airbender.JumpBranchSlt.Branch
open Arithmetic Variables Trace

/-- Trace mapping in RV32 terms, as `Comparison.RVTraceMapping`. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Name the imported operand, register, destination and PC variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.jumpBranchSlt, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .jumpBranchSlt ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- The branch's per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Circuit.Output (Nat → ZMod p) where
  satisfies := fun w =>
    Accepted trace ∧ RVPooledDecoded trace program ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- Assumptions of the RV statements: `RVTraceInputs`. No code-alignment premise is needed. -/
abbrev RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  RVTraceInputs trace initial cells program

end Airbender.JumpBranchSlt.Branch

namespace Airbender.JumpBranchSlt.Jump
open Arithmetic Variables Trace

/-- Trace mapping in RV32 terms, as `Comparison.RVTraceMapping`. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Name the imported operand, register, destination and PC variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.jumpBranchSlt, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .jumpBranchSlt ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- The jump's per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Circuit.Output (Nat → ZMod p) where
  satisfies := fun w =>
    Accepted trace ∧ RVPooledDecoded trace program ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- Assumptions of the RV statements: `RVTraceInputs`. No code-alignment premise is needed. -/
abbrev RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  RVTraceInputs trace initial cells program

end Airbender.JumpBranchSlt.Jump
