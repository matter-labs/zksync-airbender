import Airbender.Proofs.FullUnsigned.SplitMemoryCall

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem split_csr_injective : Function.Injective Keccak.Split.Kind.csr := by
  intro first last equal
  cases first <;> cases last <;> simp_all [Keccak.Split.Kind.csr]

variable [Fact babyBearModulus.Prime]

/-- Exact public lookup and native request matching identify the original
split instruction, its full PC and its actual worker kind. -/
theorem unrolled_full_split_caller_source
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (cached : Bool) (worker : Keccak.Split.Native.Row babyBearModulus)
    (matched : worker.fulfillment cached = Delegation.Requests.caller row.assignment) :
    ∃ entry ∈ FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text,
      entry.SourceWith initial Keccak.Split.Caller.decoderFields ∧
      row.start.word.toBitVec = entry.pc ∧
      Delegation.Caller.nativeQuery row.assignment = Keccak.Split.Caller.query entry ∧
      worker.kind = entry.data.family := by
  have csr := congrArg Delegation.Requests.Request.csr matched
  change worker.kind.csr = (Delegation.Requests.caller row.assignment).csr at csr
  rcases unrolled_full_native_row_classification setup lookup accepted excluded initialPC row member with
    ⟨_, _, _, _, _, ordinary⟩ | ⟨entry, _, _, _, query, _⟩ | ⟨entry, included, source, _, query, _⟩
  · exact False.elim (ordinary ⟨family, selected⟩)
  · rw [Delegation.Caller.Proofs.query_csr (by decide) query] at csr
    cases actual : worker.kind <;> cases expected : entry.data.family <;>
      norm_num [actual, expected, Keccak.Split.Kind.csr, Delegation.Requests.csr] at csr
  · have sameKind := split_csr_injective (csr.trans
      (Keccak.Split.Native.Proofs.caller_csr_of_query (by decide) query))
    have low := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[0]) query
    have high := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[1]) query
    change row.assignment 0 = ((Word.ofBitVec entry.pc).lo : ZMod babyBearModulus) at low
    change row.assignment 1 = ((Word.ofBitVec entry.pc).hi : ZMod babyBearModulus) at high
    have word : row.start.word = Word.ofBitVec entry.pc := by
      cases row with
      | mk kind assignment =>
        cases family
        exact word_of_pc_query (by decide) low high
    exact ⟨entry, included, source,
      (congrArg Word.toBitVec word).trans (Word.ofBitVec_roundtrip _), query, sameKind⟩

end Airbender.Compiler.MachineTargets.Proofs
