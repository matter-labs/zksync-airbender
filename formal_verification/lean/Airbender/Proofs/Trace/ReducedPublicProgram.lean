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

/-- The reduced native preprocessor admits only the BLAKE2 extended-round CSR
among virtual caller words. This follows from the public text projection. -/
theorem reduced_delegation_csr {csr : Nat}
    (allowed : Config.reduced.delegationCSR csr = true) : csr = 0x7c7 := by
  unfold Config.delegationCSR at allowed
  split at allowed <;> simp_all

theorem reduced_caller_program (initial : State) (text : List (BitVec 32)) :
    ∀ caller ∈ callerProgramOf .reduced initial text, caller.csr = 0x7c7 := by
  intro caller member
  obtain ⟨⟨bits, index⟩, _, selected⟩ := List.mem_filterMap.mp member
  unfold callerEntry callerEntryWith at selected
  cases decoded : SailRV32.Functions.encdec_backwards bits with
  | impure call continuation => simp [decoded] at selected
  | pure instruction =>
    simp only [decoded, bind, Option.bind] at selected
    split at selected
    next address source destination =>
      split at selected
      next admitted =>
        cases selected
        simp only [Bool.and_eq_true, beq_iff_eq] at admitted
        exact reduced_delegation_csr admitted.2
      next rejected => simp at selected
    next => simp at selected

/-- No special5 exclusion has to be supplied separately for reduced text. -/
theorem reduced_no_special5 (initial : State) (text : List (BitVec 32)) :
    NoSpecial5Call (callerProgramOf .reduced initial text) := by
  intro caller member
  rw [reduced_caller_program initial text caller member]
  decide

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
