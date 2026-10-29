import Airbender.Review.Helpers.Decoder.ProgramRows
import Airbender.Proofs.Trace.ReducedInclusion

namespace Airbender.Trace.NativeDecoder.ProgramRows.Proofs
open Airbender.Trace.NativeDecoder.ProgramRows
open Airbender.AddSub.Modular.External.Caller
open Reference.RiscV.Sail
set_option warningAsError true

/-- The public reduced decoder uses exactly the same four-family filter as the
stream-aware reduced machine. -/
theorem reduced_decoder_fields_eq (instruction : SailRV32.instruction) :
    reducedDecoderFields instruction = Config.reduced.fields instruction := by
  rfl

/-- A selected reduced decoder entry belongs to one of the four circuits
present in the native reduced setup. -/
theorem reduced_fields_family {instruction : SailRV32.instruction}
    {data : DecoderData PooledFamily}
    (selected : Config.reduced.fields instruction = some data) :
    reducedFamily data.family = true := by
  cases base : AddSub.Modular.External.decoderFields instruction with
  | none => simp [Config.fields, base] at selected
  | some raw =>
    cases fam : raw.family <;> simp_all [Config.fields, reducedFamily]

/-- Public reduced text cannot introduce a row from the absent MUL/DIV or
subword-memory circuits. Unsupported words are simply absent. -/
theorem reduced_program_family (initial : State) (text : List (BitVec 32)) :
    ∀ entry ∈ programOf .reduced initial text,
      reducedFamily entry.data.family = true := by
  intro entry member
  obtain ⟨⟨bits, index⟩, _, selected⟩ := List.mem_filterMap.mp member
  unfold wordEntry at selected
  cases decoded : SailRV32.Functions.encdec_backwards bits with
  | impure call continuation => simp [decoded] at selected
  | pure instruction =>
    cases fields : Config.reduced.fields instruction with
    | none => simp [decoded, fields] at selected
    | some data =>
      simp only [decoded, fields, bind, Option.bind] at selected
      change (some ⟨BitVec.ofNat 32 (4 * index), bits, instruction, data⟩ :
        Option PooledProgramEntry) = some entry at selected
      cases selected
      exact reduced_fields_family fields

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The reduced-family hypothesis in the run-inclusion theorem follows from
the supplied public text rather than a private witness or separate promise. -/
theorem public_text_realizes_reduced {p : Nat} [Fact p.Prime]
    (stream : List (BitVec 32)) (initial : State) (text : List (BitVec 32))
    (callers : List Delegation.Caller.ProgramEntry)
    (trace : PooledTrace p) (cells : List Cell)
    (view : MemoryToken p → MemoryToken p)
    (run : AddSub.Modular.External.Caller.Realizes reducedCall stream
      (programOf .reduced initial text)
      callers trace initial cells view) :
    ReducedRealizes stream (programOf .reduced initial text)
      callers trace initial cells view :=
  realizes_reduced stream (programOf .reduced initial text) callers trace initial
    cells view (reduced_program_family initial text) run

end Airbender.Trace.NativeDecoder.ProgramRows.Proofs
