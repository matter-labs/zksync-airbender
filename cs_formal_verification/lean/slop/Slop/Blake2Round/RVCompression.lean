module
public import Slop.Blake2Round.RVCallSteps
public import Slop.Blake2Round.RVSpec
public import Slop.Blake2Round.RVWords
public import Slop.Delegation.ReverseFold
public import Slop.Defs.Trace.Workers.Blake2Round.Call

@[expose] public section

/-! RV twins of `CallCompression.lean` and `CompressionBinding.lean`, plus the delegate link: the complete
    extended-BLAKE span on `RV.State`s reaches the 7/10-round reference, and its final state is the spec's run of the
    span's round delegation calls (`RV.calls (rvCalls flags)`). RAM cells include the shadow RAM below `ROM_END`. -/

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

private theorem offset_address (pointer : BitVec 32) (k : Nat) :
    pointer + 32#32 + BitVec.ofNat 32 (4 * k) = pointer + BitVec.ofNat 32 (4 * (8 + k)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have thirtyTwo : (32#32).toNat = 32 := by rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, thirtyTwo]
  omega

/-- The aligned words after storing the 8 chaining and 16 working words at a 128-aligned `pointer`: the circuit's
    post-state `T` reads the same words as the spec's stores on the pre-state `S`. -/
theorem two_block_words {S T : RV.State} {pointer : BitVec 32} {first : Vector RV.Word 8}
    {second : Vector RV.Word 16} (pointerAligned : pointer.toNat % 128 = 0)
    (stateWords : (rvBlockWords T pointer 8 0).map Word.toBitVec = first)
    (extendedWords : (rvBlockWords T pointer 16 8).map Word.toBitVec = second)
    (words : ∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 24, a ≠ pointer + BitVec.ofNat 32 (4 * j.val)) →
      RV.read T.mem a 4 = RV.read S.mem a 4) :
    ∀ a : BitVec 32, a.toNat % 4 = 0 →
      RV.read T.mem a 4 =
        RV.read (S.storeAll (RV.writesAt pointer first ++ RV.writesAt (pointer + 32#32) second)).mem a 4 := by
  have fits : pointer.toNat + 96 ≤ 2 ^ 32 := by have := pointer.isLt; omega
  have secondAt : (pointer + 32#32).toNat = pointer.toNat + 32 := by
    have thirtyTwo : (32#32).toNat = 32 := by rfl
    simp only [BitVec.toNat_add, thirtyTwo]
    omega
  intro a alignedA
  by_cases inState : ∃ j : Fin 8, a = pointer + BitVec.ofNat 32 (4 * j.val)
  · obtain ⟨j, rfl⟩ := inState
    have spec := read_writesAt_at S [] (RV.writesAt (pointer + 32#32) second) pointer first (by omega)
      (by
        intro aw member
        obtain ⟨k, kBound, address⟩ := RV.writesAt_addr (pointer + 32#32) second (by omega) aw member
        omega) j
    simp only [List.nil_append] at spec
    rw [spec]
    have entry := congrArg (fun words : Vector RV.Word 8 => words[j]) stateWords
    simp only [rvBlockWords, rvRamEncoding, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn,
      Word.ofBitVec_roundtrip, Nat.zero_add] at entry
    exact entry
  by_cases inExtended : ∃ k : Fin 16, a = pointer + BitVec.ofNat 32 (4 * (8 + k.val))
  · obtain ⟨k, rfl⟩ := inExtended
    have spec := read_writesAt_at S (RV.writesAt pointer first) [] (pointer + 32#32) second (by omega)
      (by simp) k
    simp only [List.append_nil, offset_address] at spec
    rw [spec]
    have entry := congrArg (fun words : Vector RV.Word 16 => words[k]) extendedWords
    simp only [rvBlockWords, rvRamEncoding, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn,
      Word.ofBitVec_roundtrip] at entry
    exact entry
  have outsideFirst : ∀ j : Fin 8, a ≠ pointer + BitVec.ofNat 32 (4 * j.val) :=
    fun j same => inState ⟨j, same⟩
  have outsideSecond : ∀ k : Fin 16, a ≠ pointer + 32#32 + BitVec.ofNat 32 (4 * k.val) := by
    intro k same
    rw [offset_address] at same
    exact inExtended ⟨k, same⟩
  have outside : ∀ j : Fin 24, a ≠ pointer + BitVec.ofNat 32 (4 * j.val) := by
    intro j same
    by_cases low : j.val < 8
    · exact outsideFirst ⟨j.val, low⟩ same
    · apply inExtended
      refine ⟨⟨j.val - 8, by omega⟩, ?_⟩
      rw [same]
      simp only [show 8 + (j.val - 8) = j.val by omega]
  rw [words a alignedA outside, RV.read_storeAll_other S _ a (by have := a.isLt; omega)]
  intro aw member
  rcases List.mem_append.mp member with inFirst | inSecond
  · exact writesAt_disjoint pointer a first (by omega) (by omega) alignedA outsideFirst aw inFirst
  · exact writesAt_disjoint (pointer + 32#32) a second (by omega) (by omega) alignedA outsideSecond aw inSecond

/-- One round call: the spec's round delegation from the circuit's pre-state (at any PC) is its post-state. -/
theorem round_call_link {S T : RV.State} {statePointer messagePointer : BitVec 32} {flags : Fin 8} {r : Nat}
    (bound : r < RV.nR (reducedOf flags))
    (stateAligned : statePointer.toNat % 128 = 0) (messageAligned : messagePointer.toNat % 64 = 0)
    (separate : statePointer ≠ messagePointer)
    (step : rvPhysicalState T statePointer = Compression.step flags (Fin.ofNat 10 r)
      (rvPhysicalState S statePointer) (rvBlockWords S messagePointer 16 0))
    (x10 : S.getReg 10 = statePointer) (x11 : S.getReg 11 = messagePointer)
    (x12 : S.getReg 12 = (controlAt flags r).toBitVec) (x12' : T.getReg 12 = (controlAt flags (r + 1)).toBitVec)
    (regs : ∀ reg : BitVec 5, reg ≠ 12 → T.getReg reg = S.getReg reg)
    (words : ∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 24, a ≠ statePointer + BitVec.ofNat 32 (4 * j.val)) →
      RV.read T.mem a 4 = RV.read S.mem a 4)
    (rom : T.rom = S.rom) (input : T.input = S.input) (x : RV.Word) :
    ∃ U, RV.calls [.blakeRound] (S.setPC x) = some U ∧ RV.Same U (T.setPC (x + 4)) := by
  have r10 : r < 10 := by unfold RV.nR at bound; split at bound <;> omega
  have stateFits : statePointer.toNat + 96 ≤ 2 ^ 32 := by have := statePointer.isLt; omega
  have messageFits : messagePointer.toNat + 64 ≤ 2 ^ 32 := by have := messagePointer.isLt; omega
  have secondFits : (statePointer + 32#32).toNat = statePointer.toNat + 32 := by
    have thirtyTwo : (32#32).toNat = 32 := by rfl
    simp only [BitVec.toNat_add, thirtyTwo]
    omega
  have hBits : (rvBlockWords S statePointer 8 0).map Word.toBitVec = RV.readWords S.mem statePointer 8 :=
    rv_block_words
  have eBits : (rvBlockWords S statePointer 16 8).map Word.toBitVec =
      RV.readWords S.mem (statePointer + 32#32) 16 := by
    rw [rv_block_words_offset]
  have mBits : (rvBlockWords S messagePointer 16 0).map Word.toBitVec = RV.readWords S.mem messagePointer 16 :=
    rv_block_words
  have bounded {n offset : Nat} {pointer : BitVec 32} : ∀ i : Fin n, (rvBlockWords S pointer n offset)[i].Bounded := by
    intro i
    simp only [rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, rvRamEncoding]
    exact Word.ofBitVec_bound _
  obtain ⟨extendedEq, stateEq⟩ := step_effect flags bound (rvBlockWords S statePointer 8 0)
    (rvBlockWords S statePointer 16 8) (rvBlockWords S messagePointer 16 0) bounded bounded bounded
  have physical := congrArg Prod.fst step
  have physical' := congrArg Prod.snd step
  simp only [rvPhysicalState] at physical physical'
  rw [← physical] at stateEq
  rw [← physical'] at extendedEq
  rw [hBits, eBits, mBits] at extendedEq stateEq
  have effectCall := RV.blakeRound_mode_call S.mem statePointer messagePointer
    ⟨stateAligned, by simp only [RV.RAM_END]; omega⟩ ⟨messageAligned, by simp only [RV.RAM_END]; omega⟩ separate
    (reducedOf flags) (rightOf flags) (compressionOf flags) r bound
  simp only at effectCall
  have controlNow := controlAt_toBitVec flags ⟨r, by omega⟩
  have controlNext := controlAt_toBitVec flags ⟨r + 1, by omega⟩
  simp only at controlNow controlNext
  rw [← controlNow] at effectCall
  have stateWords := stateEq
  have extendedWords := extendedEq
  obtain ⟨U, call, same⟩ := call_same (S := S.setPC x) (T := T) (k := .blakeRound)
    (by
      change RV.Delegation.blakeRound (S.getReg 10) (S.getReg 11) (S.getReg 12) S.mem = _
      rw [x10, x11, x12]
      exact effectCall)
    (by
      intro aw member
      rcases List.mem_append.mp member with first | second
      · exact (RV.writesAt_in statePointer _ (by omega) (by simp only [RV.RAM_END]; omega) aw first).1
      · exact (RV.writesAt_in (statePointer + 32#32) _ (by omega) (by simp only [RV.RAM_END]; omega) aw second).1)
    rom input
    (by
      intro reg
      by_cases r12 : reg = 12
      · subst r12
        simp only [true_and, show (12 : BitVec 5) ≠ 0 by decide, ne_eq, not_false_eq_true, ite_true]
        rw [x12', controlNext]
      · simp only [r12, false_and, ite_false]
        exact regs reg r12)
    (by
      intro a alignedA
      rw [storeAll_setPC]
      exact two_block_words stateAligned stateWords extendedWords words a alignedA)
  exact ⟨U, call, same⟩

/-- The complete extended-BLAKE span over `RV.State`s from a proof-level RV boundary: the reference compression on
    actual RV RAM, the trace mapping, and the delegate link. -/
theorem rv_compression_binding_at_boundary [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Word 16) (output : Compression.State),
      Compression.RVWordMapping initial after statePointer messagePointer input output message ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output = Compression.run flags input message ∧
        ∃ s', RV.calls (rvCalls flags) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls flags).length))) := by
  obtain ⟨statePointer, messagePointer, after, states, count, stateRead, messageRead, stateAligned, messageAligned,
    separate, head, last, trace, steps⟩ := rv_call_steps hp inverse accepted inputs aligned
  have endpoints : states[0]'(by omega) = after ∧ states[data.rows.length]'(by omega) = initial := by
    constructor
    · have first := head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at first
      exact Option.some.inj first
    · have finish := List.getLast_of_getLast?_eq_some last
      simpa only [List.getLast_eq_getElem, count, Nat.add_sub_cancel] using finish
  let physical := fun i : Fin (data.rows.length + 1) =>
    rvPhysicalState (states[i.val]'(by omega)) statePointer
  let message := fun i : Fin (data.rows.length + 1) =>
    rvBlockWords (states[i.val]'(by omega)) messagePointer 16 0
  have unchanged := reverse_constant message (fun i => (steps i).2.1)
  have result := reverse_fold physical
    (fun round state => Compression.step flags (Fin.ofNat 10 round) state (message ⟨data.rows.length, by omega⟩))
    (fun i => by
      have current := (steps i).1
      rw [show rvBlockWords (states[i.val + 1]'(by omega)) messagePointer 16 0 =
        message ⟨data.rows.length, by omega⟩ from unchanged ⟨i.val + 1, by omega⟩] at current
      exact current)
  have state4 : statePointer.toNat % 4 = 0 := by omega
  have message4 : messagePointer.toNat % 4 = 0 := by omega
  refine ⟨after, statePointer, messagePointer, rvPhysicalState initial statePointer,
    rvBlockWords initial messagePointer 16 0, rvPhysicalState after statePointer,
    ⟨⟨stateRead, messageRead⟩, rv_block_at state4, rv_block_at state4, rv_block_at message4,
      rv_block_at state4, rv_block_at state4⟩, trace, ?_, ?_⟩
  · have folded : rvPhysicalState after statePointer =
        Fin.foldl data.rows.length (fun state i => Compression.step flags (Fin.ofNat 10 i.val) state
          (rvBlockWords initial messagePointer 16 0)) (rvPhysicalState initial statePointer) := by
      simpa only [physical, message, endpoints.1, endpoints.2] using result
    have countEq := congrArg (fun n => Fin.foldl n
      (fun state i => Compression.step flags (Fin.ofNat 10 i.val) state
        (rvBlockWords initial messagePointer 16 0)) (rvPhysicalState initial statePointer)) inputs.calls
    exact folded.trans countEq
  · let n := data.rows.length
    let chron : Nat → RV.State := fun j => states[n - j]'(by omega)
    have nBound : n = RV.nR (reducedOf flags) := by simp only [n, inputs.calls, calls_eq_nR]
    have link := calls_replicate_link (k := .blakeRound) (n := n) chron (by
      intro m bound x
      have step := steps ⟨n - 1 - m, by omega⟩
      simp only [show n - 1 - m + 1 = n - m by omega, show data.rows.length - 1 - (n - 1 - m) = m by omega]
        at step
      obtain ⟨physicalStep, _, x10, x11, x12, x12', regs, words, rom, input⟩ := step
      have next : chron (m + 1) = states[n - 1 - m]'(by omega) := by
        simp only [chron, show n - (m + 1) = n - 1 - m by omega]
      rw [next]
      exact round_call_link (by omega) stateAligned messageAligned separate physicalStep x10 x11 x12 x12' regs
        words rom input x)
    have first : chron 0 = initial := by simpa only [chron, Nat.sub_zero] using endpoints.2
    have final : chron n = after := by simpa only [chron, Nat.sub_self] using endpoints.1
    rw [first, final] at link
    have length : (rvCalls flags).length = n := by simp only [rvCalls, List.length_replicate, n, inputs.calls]
    rw [length]
    simpa only [rvCalls, n, inputs.calls] using link

end Airbender.Blake2Round.Proofs
