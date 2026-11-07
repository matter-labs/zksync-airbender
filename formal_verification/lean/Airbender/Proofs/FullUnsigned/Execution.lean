import Airbender.Review.Trace.FullUnsigned
import Airbender.Proofs.GKRProtocol.TextImage

namespace Airbender.FullUnsigned.Proofs
open Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- Typed caller entries are justified by successful reads of the supplied
public text and the original pure Sail decoder, for any metadata registry. -/
theorem text_sources {Family : Type}
    (fields : SailRV32.instruction → Option (DecoderData Family))
    (initial : State) (text : List (BitVec 32))
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    ∀ entry ∈ entriesWith fields text, entry.SourceWith initial fields := by
  intro entry member
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  have found : text[index]? = some bits := List.mk_mem_zipIdx_iff_getElem?.mp inText
  have indexBound : index < text.length := by
    by_contra notBound
    have : text[index]? = none := by simp [Nat.le_of_not_gt notBound]
    rw [this] at found
    contradiction
  have value : text[index] = bits := by
    have : text[index]? = some text[index] := by simp [indexBound]
    rw [this] at found
    exact Option.some.inj found
  have bytes : (Cell.ram (BitVec.ofNat 32 (4 * index))).read initial =
      .ok bits initial := by
    simpa only [value] using ROM.Proofs.bytes_of_text_image initial text image size
      ⟨index, indexBound⟩
  cases decoded : SailRV32.Functions.encdec_backwards bits with
  | pure instruction =>
    cases projected : fields instruction with
    | none => simp [decoded, projected] at selected
    | some data =>
      simp only [decoded, projected, bind, Option.bind] at selected
      change (some ⟨BitVec.ofNat 32 (4 * index), bits, instruction, data⟩ :
        Option (Trace.ProgramEntry Family)) = some entry at selected
      cases selected
      exact ⟨bytes, by rw [decoded]; rfl, projected⟩
  | impure call continuation => simp [decoded] at selected


variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

theorem standard_step {stream : List (BitVec 32)} {program : Program}
    {before after : State × Nat}
    (step : AddSub.Modular.External.Caller.Step standardCall stream
      program.ordinary program.callers before after) :
    Step stream program before after := Or.inl step

theorem ordinary_step {stream : List (BitVec 32)} {program : Program}
    {before after : State × Nat}
    (step : NonDeterminism.StepWithClause AddSub.Modular.External.decoderFields
      AddSub.Modular.External.clause stream program.ordinary before after) :
    Step stream program before after := Or.inl (Or.inl step)

theorem split_step {stream : List (BitVec 32)} {program : Program}
    {before after : State × Nat}
    (step : SplitCallStep program.splitCallers before after) :
    Step stream program before after := Or.inr step

/-- A complete split reference call retires in the same stream position. -/
theorem split_call {stream : List (BitVec 32)} {program : Program}
    {before after : State} (position : Nat)
    {entry : Keccak.Split.Caller.ProgramEntry} (member : entry ∈ program.splitCallers)
    (source : entry.SourceWith before Keccak.Split.Caller.decoderFields)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok entry.pc before)
    (retirement : Keccak.Split.Call.Retires entry.data.family before after) :
    Step stream program (before, position) (after, position) :=
  Or.inr ⟨rfl, entry, member, source, pc, retirement⟩

end Airbender.FullUnsigned.Proofs
