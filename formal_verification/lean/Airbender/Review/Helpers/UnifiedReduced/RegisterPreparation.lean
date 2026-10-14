import Airbender.Review.Helpers.UnifiedReduced.PCRelativePreparation

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- The original Sail immediate extension, added to the actual source operand. -/
def registerImmediateValue (value : BitVec 32) (immediate : BitVec 12) : BitVec 32 :=
  value + SailRV32.Functions.sign_extend (m := 32) immediate

/-- Public modular code identifies a final register-dependent ADDI. Only that
    final cycle is worker-free; earlier issued and unissued effects remain. -/
structure RegisterImmediatePreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat)
    (source register : BitVec 5) (immediate : BitVec 12) : Prop where
  registry : WrappedSequentialProgram program
  atCut : ∀ entry ∈ program, entry.pc = wrappedProgramAddress data (cut - 4) →
    entry.instruction = .ITYPE (immediate, .Regidx source, .Regidx register, .ADDI)
  prefixScope : data.workers.windowRows (cut - 4) cut = []
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Both reads come from the same actual preparation cycle, including aliases.
    The canonical output token retains its native timestamp. No operand or
    prepared value is supplied as an input. -/
def RegisterImmediatePreparedControl [Fact p.Prime] (tokens : List (MemoryToken p))
    (before after : State) (cut : Nat) (source register : BitVec 5) (immediate : BitVec 12) : Prop :=
  ∃ value : BitVec 32,
    (Cell.register source).read before = .ok value before ∧
    (Cell.register register).read after = .ok (registerImmediateValue value immediate) after ∧
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧
      token.word = Word.ofBitVec (registerImmediateValue value immediate)

end Airbender.UnifiedReduced.Caller
