import Slop.Blake2Round.StateTrace
import Slop.Blake2Round.PhysicalWords
import Slop.Delegation.ReverseFold

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem call_compression [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (statePointer messagePointer : BitVec 32) (after : State),
      (Cell.register 10).read initial = .ok statePointer initial ∧
      (Cell.register 11).read initial = .ok messagePointer initial ∧
      Delegation.TraceMapping data initial after cells ∧
      (∀ cell ∈ cells, ∃ value, cell.read after = .ok value after) ∧
      physicalState after statePointer = Compression.run flags
        (physicalState initial statePointer) (blockWords initial messagePointer 16 0) := by
  obtain ⟨statePointer, messagePointer, ascending, count, after, states, stateCount,
    stateRead, messageRead, permutation, head, last, trace, readable, effects⟩ :=
    call_state_trace hp inverse accepted inputs aligned
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have bounds := operation_word_bounds_at_boundary hp inverse accepted (call_operation_inputs clockBound accepted inputs)
  have modes := call_modes clockBound accepted inputs
  have endpoints : states[0]'(by omega) = after ∧ states[data.rows.length]'(by omega) = initial := by
    constructor
    · have first := head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at first
      exact Option.some.inj first
    · have finish := List.getLast_of_getLast?_eq_some last
      simpa only [List.getLast_eq_getElem, stateCount, Nat.add_sub_cancel] using finish
  let physical := fun i : Fin (data.rows.length + 1) =>
    physicalState (states[i.val]'(by omega)) statePointer
  let message := fun i : Fin (data.rows.length + 1) =>
    blockWords (states[i.val]'(by omega)) messagePointer 16 0
  have transitions : ∀ i : Fin data.rows.length,
      physical ⟨i.val, by omega⟩ =
        Compression.step flags (Fin.ofNat 10 (data.rows.length - 1 - i.val))
          (physical ⟨i.val + 1, by omega⟩) (message ⟨i.val + 1, by omega⟩) ∧
      message ⟨i.val, by omega⟩ = message ⟨i.val + 1, by omega⟩ := by
    intro i
    let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
    have member : row ∈ data.rows :=
      ((List.reverse_perm ascending).trans permutation).mem_iff.mp (List.getElem_mem _)
    obtain ⟨round, roundIndex, effect, _, _, _, observed⟩ := effects i
    have native : row = ⟨.blakeRound, row.assignment⟩ := by
      have native : row = ⟨row.family, row.assignment⟩ := rfl
      simpa only [inputs.family row member] using native
    have reads : ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
        (readToken row.assignment port).word.Bounded := by
      simpa only [← native] using bounds.reads row member
    have writes : ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
        ((⟨.blakeRound, row.assignment⟩ : Delegation.Row p).writeToken port).word.Bounded := by
      simpa only [← native] using bounds.writes row member
    have words := physical_row_words round (native_encoded_words reads writes observed)
    have stateBound : ∀ index : Fin 8, (Native.output row.assignment).state[index].Bounded := by
      intro index
      rw [words.2.2.2.1]
      simpa only [physicalState, blockWords, Fin.getElem_fin, Vector.getElem_ofFn, ramEncoding] using
        Word.ofBitVec_bound (BitVec.ofNat 32 (ramWord (states[i.val]'(by omega))
          (statePointer + BitVec.ofNat 32 (4 * (0 + index.val)))))
    have extendedBound : ∀ index : Fin 16, (Native.output row.assignment).extended[index].Bounded := by
      intro index
      rw [words.2.2.2.2.1]
      simpa only [physicalState, blockWords, Fin.getElem_fin, Vector.getElem_ofFn, ramEncoding] using
        Word.ofBitVec_bound (BitVec.ofNat 32 (ramWord (states[i.val]'(by omega))
          (statePointer + BitVec.ofNat 32 (4 * (8 + index.val)))))
    have reference := row_compression effect (modes row member round) stateBound extendedBound
    rw [show (Native.input round row.assignment).round = round from rfl] at reference
    rw [words.1, words.2.1, words.2.2.1, words.2.2.2.1, words.2.2.2.2.1] at reference
    have roundEq : round = Fin.ofNat 10 (data.rows.length - 1 - i.val) := by
      apply Fin.ext
      simp only [Fin.val_ofNat]
      rw [← roundIndex, Nat.mod_eq_of_lt round.isLt]
    exact ⟨by simpa only [roundEq, physical, message, physicalState] using reference,
      by simpa only [message] using words.2.2.2.2.2.symm⟩
  have unchanged := reverse_constant message (fun i => (transitions i).2)
  have result := reverse_fold physical
    (fun round state => Compression.step flags (Fin.ofNat 10 round) state (message ⟨data.rows.length, by omega⟩))
    (fun i => by
      have current := (transitions i).1
      rw [unchanged ⟨i.val + 1, by omega⟩] at current
      exact current)
  refine ⟨statePointer, messagePointer, after, stateRead, messageRead, trace, ?_, ?_⟩
  · simpa only [endpoints.1] using readable 0 (by omega)
  · have folded : physicalState after statePointer =
        Fin.foldl data.rows.length (fun state i => Compression.step flags (Fin.ofNat 10 i.val) state
          (blockWords initial messagePointer 16 0)) (physicalState initial statePointer) := by
      simpa only [physical, message, endpoints.1, endpoints.2] using result
    have countEq := congrArg (fun n => Fin.foldl n
      (fun state i => Compression.step flags (Fin.ofNat 10 i.val) state
        (blockWords initial messagePointer 16 0)) (physicalState initial statePointer)) inputs.calls
    exact folded.trans countEq

end Airbender.Blake2Round.Proofs
