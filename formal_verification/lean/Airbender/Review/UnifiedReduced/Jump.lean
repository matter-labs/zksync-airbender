import Airbender.Review.UnifiedReduced.Decoder
import Airbender.Review.UnifiedReduced.Setup
import Airbender.Review.JumpBranchSlt.Jump

namespace Airbender.UnifiedReduced.Jump
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace
abbrev Input := JumpBranchSlt.Jump.Input

/-- Canonical source, offset, link and PC words. Placement numbers are confined
    here; the trace interface only names these observations. -/
def sourceWord (w : Nat → ZMod p) : Word := ⟨(w 36).val, (w 37).val⟩
def offsetWord (w : Nat → ZMod p) : Word := ⟨(w 8).val, (w 9).val⟩
def initialPC (w : Nat → ZMod p) : Word := ⟨(w 0).val, (w 1).val⟩
def destination (w : Nat → ZMod p) : Word := ⟨(w 50).val, (w 51).val⟩
def finalPC (w : Nat → ZMod p) : Word := ⟨(w 30).val, (w 31).val⟩

/-- Identify the represented words; no ranges or correct jump result are required. -/
structure WordMapping (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  source : input.source = sourceWord w
  offset : input.offset = offsetWord w
  pc : input.pc = initialPC w
  result : output.destination = destination w
  nextPC : output.pc = finalPC w

/-- The original Sail jump constructor, including its encoded offset and registers. -/
abbrev instruction (input : Input) : SailRV32.instruction :=
  JumpBranchSlt.Jump.instruction input

/-- Locate this row in initialized history and the actual public program.
    History supplies the source read; public decoding supplies selectors and
    offset extension. Neither is a caller-provided instruction result. -/
structure TraceMapping [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  state : RowPosition trace initial cells ⟨.machine, w⟩ input.before
  instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧ entry.instruction = instruction input

/-- Public initialization/table and Sail configuration conditions. Four-byte
    code alignment selects Airbender's instruction profile. Shared history and
    queries derive all per-row ranges, reads and target/link effects. Unlike the
    standalone jump artifact, unified rows range both final PC limbs locally. -/
structure InterfaceAssumptions [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop where
  initialization : NativeInputs decoderFields trace initial cells program
  setup : trace.rom = Setup.table initial
  codeAligned : ∀ entry ∈ program, entry.pc.toNat % 4 = 0
  isa : ∃ value, initial.regs.get? .misa = some value
  landingPad : input.instruction.indirect = true →
    initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0

/-- Imported native equations, logical matching and public decoder membership,
    interpreted by the named mapping above. JAL/JALR use the same initialized
    history as arithmetic and memory rows. -/
def circuitModel [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

end Airbender.UnifiedReduced.Jump
