import Slop.Blake2G.RVCallSteps
import Slop.Blake2G.RVSpec
import Slop.Blake2G.CallWorkVector
import Slop.Delegation.ReverseFold
import Slop.Blake2Round.RVWords

/-! RV twins of `CallWorkVector.lean` and `WorkVectorBinding.lean`, plus the delegate link: the complete G span on
    `RV.State`s reaches the 56/80-call reference, and its final state is the spec's run of the span's `G` delegation
    calls (`RV.calls (rvCalls reduced)`). RAM cells include the shadow RAM below `ROM_END`. -/

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
open Blake2Round.Proofs (rv_block_at rv_block_words)
set_option warningAsError true
set_option maxRecDepth 16384
attribute [local irreducible] Specs.BLAKE3.g
set_option backward.isDefEq.respectTransparency false

theorem rv_physical_reference_step (reduced : Bool) (call : Nat) {before after : RV.State}
    {state message : BitVec 32}
    (correct : Blake2G.State.spec (rvPhysicalInput (controllerAt reduced call) before state message)
      (rvPhysicalWords after state)) :
    (rvPhysicalWords after state).map Word.value = WorkVector.step reduced call
      (rvPhysicalWords before message) ((rvPhysicalWords before state).map Word.value) := by
  let controller := controllerAt reduced call
  have stateIndex (index : Fin 4) :
      Fin.ofNat 16 (Control.step controller).stateOffsets[index] = (stateLanes controller)[index] := by
    apply Fin.ext
    simp only [Fin.val_ofNat, stateLanes, Fin.getElem_fin, Vector.getElem_ofFn]
    exact Nat.mod_eq_of_lt (Control.Proofs.state_offsets_bounded controller index)
  have messageIndex (index : Fin 2) :
      (rvPhysicalWords before message)[Fin.ofNat 16 (Control.step controller).messageOffsets[index]] =
        (rvPhysicalWords before message)[(Control.step controller).messageOffsets[index]]'
          (Control.Proofs.message_offsets_bounded controller index) := by
    have bounded := Control.Proofs.message_offsets_bounded controller index
    simp only [Fin.getElem_fin] at bounded
    simp only [Fin.getElem_fin, Fin.val_ofNat, Nat.mod_eq_of_lt bounded]
  dsimp only [controller] at stateIndex messageIndex
  unfold Blake2G.State.spec at correct
  dsimp only [rvPhysicalInput] at correct
  dsimp only [WorkVector.step]
  rw [stateIndex 0, stateIndex 1, stateIndex 2, stateIndex 3]
  apply correct.trans
  apply congrArg₂
  · exact congrArg Word.value (messageIndex 0).symm
  · exact congrArg Word.value (messageIndex 1).symm

theorem controlAt_mod_toBitVec (reduced : Bool) (k : Nat) :
    (controlAt reduced k).toBitVec = RV.gCtl reduced (k % RV.nG reduced) := by
  have same : controlAt reduced k = controlAt reduced (k % callCount reduced) := by
    simp only [controlAt, Nat.mod_mod]
  rw [same, controlAt_toBitVec reduced (Nat.mod_lt _ (by cases reduced <;> decide)), callCount_eq_nG]

/-- One G call: the spec's `G` delegation from the circuit's pre-state (at any PC) is its post-state. -/
theorem g_call_link {S T : RV.State} {statePointer messagePointer : BitVec 32} {reduced : Bool} {m : Nat}
    (bound : m < callCount reduced)
    (stateAligned : statePointer.toNat % 64 = 0) (messageAligned : messagePointer.toNat % 64 = 0)
    (separate : statePointer ≠ messagePointer)
    (spec : Blake2G.State.spec (rvPhysicalInput (scheduledController reduced m bound) S statePointer messagePointer)
      (rvPhysicalWords T statePointer))
    (x10 : S.getReg 10 = statePointer) (x11 : S.getReg 11 = messagePointer)
    (x12 : S.getReg 12 = (controlAt reduced m).toBitVec) (x12' : T.getReg 12 = (controlAt reduced (m + 1)).toBitVec)
    (regs : ∀ r : BitVec 5, r ≠ 12 → T.getReg r = S.getReg r)
    (words : ∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 16, a ≠ statePointer + BitVec.ofNat 32 (4 * j.val)) →
      RV.read T.mem a 4 = RV.read S.mem a 4)
    (rom : T.rom = S.rom) (input : T.input = S.input) (x : RV.Word) :
    ∃ U, RV.calls [.blakeG] (S.setPC x) = some U ∧ RV.Same U (T.setPC (x + 4)) := by
  have stateFits : statePointer.toNat + 64 ≤ 2 ^ 32 := by have := statePointer.isLt; omega
  have messageFits : messagePointer.toNat + 64 ≤ 2 ^ 32 := by have := messagePointer.isLt; omega
  have nGBound : m < RV.nG reduced := callCount_eq_nG reduced ▸ bound
  let v := RV.gStep (RV.readWords S.mem messagePointer 16) m (RV.readWords S.mem statePointer 16)
  have effect : RV.Delegation.effect .blakeG ((S.setPC x).getReg 10) ((S.setPC x).getReg 11)
      ((S.setPC x).getReg 12) (S.setPC x).mem =
      some { writes := RV.writesAt statePointer v, reg := 12, val := RV.gCtl reduced ((m + 1) % RV.nG reduced) } := by
    change RV.Delegation.blakeG (S.getReg 10) (S.getReg 11) (S.getReg 12) S.mem = _
    rw [x10, x11, x12, controlAt_toBitVec reduced bound]
    exact RV.blakeG_call S.mem statePointer messagePointer ⟨stateAligned, by simp only [RV.RAM_END]; omega⟩
      ⟨messageAligned, by simp only [RV.RAM_END]; omega⟩ separate reduced m nGBound
  have reference := rv_physical_reference_step reduced m spec
  have bounded (words : Vector Word 16) (same : words = rvBlockWords S statePointer 16 0 ∨
      words = rvBlockWords S messagePointer 16 0) : ∀ i : Fin 16, words[i].Bounded := by
    intro i
    rcases same with rfl | rfl <;>
      simp only [rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, rvRamEncoding] <;>
      exact Word.ofBitVec_bound _
  have stepEq := step_gStep reduced bound (rvPhysicalWords S messagePointer) (rvPhysicalWords S statePointer)
    (bounded _ (Or.inr rfl)) (bounded _ (Or.inl rfl))
  rw [rv_block_words, rv_block_words, ← reference] at stepEq
  have output : (rvPhysicalWords T statePointer).map Word.toBitVec = v := by
    change _ = RV.gStep (RV.readWords S.mem messagePointer 16) m (RV.readWords S.mem statePointer 16)
    rw [← stepEq]
    apply Vector.ext
    intro i bound
    simp only [Vector.getElem_map, Word.toBitVec]
  have alignedWrites : ∀ aw ∈ RV.writesAt statePointer v, aw.1.toNat % 4 = 0 := by
    intro aw member
    exact (RV.writesAt_in statePointer v (by omega) (by simp only [RV.RAM_END]; omega) aw member).1
  obtain ⟨U, call, same⟩ := call_same (S := S.setPC x) (T := T) effect alignedWrites rom input
    (by
      intro r
      by_cases r12 : r = 12
      · subst r12
        simp only [true_and, show (12 : BitVec 5) ≠ 0 by decide, ne_eq, not_false_eq_true, ite_true]
        rw [x12', controlAt_mod_toBitVec]
      · simp only [r12, false_and, ite_false]
        exact regs r r12)
    (by
      intro a alignedA
      rw [storeAll_setPC]
      change RV.read T.mem a 4 = RV.read (S.storeAll (RV.writesAt statePointer v)).mem a 4
      by_cases inside : ∃ j : Fin 16, a = statePointer + BitVec.ofNat 32 (4 * j.val)
      · obtain ⟨j, rfl⟩ := inside
        have spec := read_writesAt_at S [] [] statePointer v stateFits (by simp) j
        simp only [List.nil_append, List.append_nil] at spec
        rw [spec]
        have entry := congrArg (fun words : Vector RV.Word 16 => words[j]) output
        simp only [rvPhysicalWords, rvBlockWords, rvRamEncoding, Fin.getElem_fin, Vector.getElem_map,
          Vector.getElem_ofFn, Word.ofBitVec_roundtrip, Nat.zero_add] at entry
        exact entry
      · have outside : ∀ j : Fin 16, a ≠ statePointer + BitVec.ofNat 32 (4 * j.val) :=
          fun j same => inside ⟨j, same⟩
        rw [words a alignedA outside, RV.read_storeAll_other S _ a (by have := a.isLt; omega)
          (writesAt_disjoint statePointer a v (by omega) stateFits alignedA outside)])
  exact ⟨U, call, same⟩

/-- The complete G span over `RV.State`s from a proof-level RV boundary: the reference work vector on actual RV RAM,
    the trace mapping, and the delegate link. -/
theorem rv_workvector_binding_at_boundary [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells reduced)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : RV.State) (statePointer messagePointer : BitVec 32) (input message output : Vector Word 16),
      WorkVector.RVWordMapping initial after statePointer messagePointer input message output ∧
        Delegation.RVTraceMapping data initial after cells ∧
        output.map Word.value = WorkVector.run reduced input message ∧
        ∃ s', RV.calls (rvCalls reduced) initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length))) := by
  obtain ⟨statePointer, messagePointer, after, states, count, stateRead, messageRead, stateAligned, messageAligned,
    separate, _, head, last, trace, steps⟩ := rv_call_steps hp inverse accepted inputs aligned
  have endpoints : states[0]'(by omega) = after ∧ states[data.rows.length]'(by omega) = initial := by
    constructor
    · have first := head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at first
      exact Option.some.inj first
    · have finish := List.getLast_of_getLast?_eq_some last
      simpa only [List.getLast_eq_getElem, count, Nat.add_sub_cancel] using finish
  let physical : Fin (data.rows.length + 1) → Vector Nat 16 :=
    fun i => (rvPhysicalWords (states[i.val]'(by omega)) statePointer).map Word.value
  let message : Fin (data.rows.length + 1) → Vector Word 16 :=
    fun i => rvPhysicalWords (states[i.val]'(by omega)) messagePointer
  have unchanged := reverse_constant message (fun i => (steps i).2.1)
  have transitions : ∀ i : Fin data.rows.length,
      physical ⟨i.val, by omega⟩ = WorkVector.step reduced (data.rows.length - 1 - i.val)
        (message ⟨data.rows.length, by omega⟩) (physical ⟨i.val + 1, by omega⟩) := by
    intro i
    have current := rv_physical_reference_step reduced (data.rows.length - 1 - i.val) (steps i).1
    rw [show rvPhysicalWords (states[i.val + 1]'(by omega)) messagePointer =
      message ⟨data.rows.length, by omega⟩ from unchanged ⟨i.val + 1, by omega⟩] at current
    exact current
  have result := reverse_fold physical
    (fun call state => WorkVector.step reduced call (message ⟨data.rows.length, by omega⟩) state) transitions
  have stateAligned4 : statePointer.toNat % 4 = 0 := by omega
  have messageAligned4 : messagePointer.toNat % 4 = 0 := by omega
  refine ⟨after, statePointer, messagePointer, rvPhysicalWords initial statePointer,
    rvPhysicalWords initial messagePointer, rvPhysicalWords after statePointer,
    ⟨⟨stateRead, messageRead⟩, rv_block_at stateAligned4, rv_block_at messageAligned4, rv_block_at stateAligned4, ?_⟩,
    trace, ?_, ?_⟩
  · have final := rv_block_at (state := after) (n := 16) (offset := 0) messageAligned4
    have same : rvPhysicalWords after messagePointer = rvPhysicalWords initial messagePointer := by
      simpa only [message, endpoints.1, endpoints.2] using unchanged ⟨0, by omega⟩
    change Blake2Round.Compression.RVWordsAt after messagePointer 0 (rvPhysicalWords after messagePointer) at final
    rw [same] at final
    exact final
  · have folded : (rvPhysicalWords after statePointer).map Word.value =
        Fin.foldl data.rows.length (fun state i => WorkVector.step reduced i.val
          (rvPhysicalWords initial messagePointer) state) ((rvPhysicalWords initial statePointer).map Word.value) := by
      simpa only [physical, message, endpoints.1, endpoints.2] using result
    have countEq := congrArg (fun n => Fin.foldl n
      (fun state i => WorkVector.step reduced i.val (rvPhysicalWords initial messagePointer) state)
      ((rvPhysicalWords initial statePointer).map Word.value)) inputs.calls
    exact folded.trans countEq
  · let n := data.rows.length
    let chron : Nat → RV.State := fun j => states[n - j]'(by omega)
    have link := calls_replicate_link (k := .blakeG) (n := n) chron (by
      intro m bound x
      have step := steps ⟨n - 1 - m, by omega⟩
      have callBound : m < callCount reduced := by rw [← inputs.calls]; exact bound
      simp only [show n - 1 - m + 1 = n - m by omega, show data.rows.length - 1 - (n - 1 - m) = m by omega]
        at step
      obtain ⟨spec, _, x10, x11, x12, x12', regs, words, rom, input⟩ := step
      have next : chron (m + 1) = states[n - 1 - m]'(by omega) := by
        simp only [chron, show n - (m + 1) = n - 1 - m by omega]
      rw [next]
      exact g_call_link callBound stateAligned messageAligned separate spec x10 x11 x12 x12' regs words rom input x)
    have first : chron 0 = initial := by simpa only [chron, Nat.sub_zero] using endpoints.2
    have final : chron n = after := by simpa only [chron, Nat.sub_self] using endpoints.1
    rw [first, final] at link
    have length : (rvCalls reduced).length = n := by simp only [rvCalls, List.length_replicate, n, inputs.calls]
    rw [length]
    simpa only [rvCalls, n, inputs.calls] using link

end Airbender.Blake2G.Proofs
