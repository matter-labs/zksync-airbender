import Airbender.Proofs.FullUnsigned.SplitSource
import Airbender.Proofs.Reduced.CallerSources

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Exact combined matching identifies each standard caller's public source,
full PC and worker family. Its CSR cannot alias a split worker. -/
theorem unrolled_full_standard_caller_source
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
    (worker : Delegation.Row babyBearModulus)
    (matched : Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment) :
    ∃ entry ∈ FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text,
      entry.SourceWith initial Delegation.Caller.decoderFields ∧
      row.start.word.toBitVec = entry.pc ∧
      Delegation.Caller.nativeQuery row.assignment = Delegation.Caller.query entry ∧
      worker.family = entry.data.family := by
  have csr := congrArg Delegation.Requests.Request.csr matched
  change Delegation.Requests.csr worker.family = (Delegation.Requests.caller row.assignment).csr at csr
  rcases unrolled_full_native_row_classification setup lookup accepted excluded initialPC row member with
    ⟨_, _, _, _, _, ordinary⟩ | ⟨entry, included, source, _, query, _⟩ | ⟨entry, _, _, _, query, _⟩
  · exact False.elim (ordinary ⟨family, selected⟩)
  · have sameKind := AddSub.Modular.External.Caller.Proofs.caller_worker_family (by decide) query matched
    have word := Delegation.Caller.Proofs.query_pc (by decide) query
    have nativeWord : row.start.word = Word.ofBitVec entry.pc := by
      cases row with
      | mk kind assignment => cases family; exact word
    exact ⟨entry, included, source,
      (congrArg Word.toBitVec nativeWord).trans (Word.ofBitVec_roundtrip _), query, sameKind⟩
  · rw [Keccak.Split.Native.Proofs.caller_csr_of_query (by decide) query] at csr
    cases actual : worker.family <;> cases expected : entry.data.family <;>
      norm_num [actual, expected, Keccak.Split.Kind.csr, Delegation.Requests.csr] at csr

end Airbender.Compiler.MachineTargets.Proofs
