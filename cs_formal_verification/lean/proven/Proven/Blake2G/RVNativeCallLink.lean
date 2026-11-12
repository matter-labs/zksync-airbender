module
public import Proven.Blake2G.RVNativeReference

@[expose] public section
namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Specs.BLAKE3.g

/-- One native G call updates the actual RV state for every control byte and aligned block bases. -/
theorem native_g_call_link {S T : RV.State} {statePointer messagePointer : BitVec 32} {register : Fin 256}
    (stateAligned : statePointer.toNat % 64 = 0) (messageAligned : messagePointer.toNat % 64 = 0)
    (spec : Blake2G.State.spec (rvPhysicalInput ⟨register, true⟩ S statePointer messagePointer)
      (rvPhysicalWords T statePointer))
    (x10 : S.getReg 10 = statePointer) (x11 : S.getReg 11 = messagePointer)
    (x12 : S.getReg 12 = BitVec.ofNat 32 register.val) (x12' : T.getReg 12 = (Control.step ⟨register, true⟩).register.toBitVec)
    (regs : ∀ r : BitVec 5, r ≠ 12 → T.getReg r = S.getReg r)
    (words : ∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 16, a ≠ statePointer + BitVec.ofNat 32 (4 * j.val)) →
      RV.read T.mem a 4 = RV.read S.mem a 4)
    (rom : T.rom = S.rom) (input : T.input = S.input) (x : RV.Word) :
    ∃ U, RV.calls [.blakeG] (S.setPC x) = some U ∧ RV.Same U (T.setPC (x + 4)) := by
  have stateFits : statePointer.toNat + 64 ≤ 2 ^ 32 := by have := statePointer.isLt; omega
  have messageFits : messagePointer.toNat + 64 ≤ 2 ^ 32 := by have := messagePointer.isLt; omega
  let v := RV.gStep (RV.readWords S.mem messagePointer 16) (nativeIndex register) (RV.readWords S.mem statePointer 16)
  have effect : RV.Delegation.effect .blakeG ((S.setPC x).getReg 10) ((S.setPC x).getReg 11)
      ((S.setPC x).getReg 12) (S.setPC x).mem =
      some { writes := RV.writesAt statePointer v, reg := 12, val := (Control.step ⟨register, true⟩).register.toBitVec } := by
    change RV.Delegation.blakeG (S.getReg 10) (S.getReg 11) (S.getReg 12) S.mem = _
    rw [x10, x11, x12]
    exact native_g_effect register statePointer messagePointer S.mem stateAligned messageAligned
      (by simp only [RV.RAM_END]; omega)
  have output : (rvPhysicalWords T statePointer).map Word.toBitVec = v :=
    native_physical_reference register spec
  have alignedWrites : ∀ aw ∈ RV.writesAt statePointer v, aw.1.toNat % 4 = 0 := by
    intro aw member
    exact (RV.writesAt_in statePointer v (by omega) (by simp only [RV.RAM_END]; omega) aw member).1
  obtain ⟨U, call, same⟩ := call_same (S := S.setPC x) (T := T) effect alignedWrites rom input
    (by
      intro r
      by_cases r12 : r = 12
      · subst r12
        simp only [true_and, show (12 : BitVec 5) ≠ 0 by decide, ne_eq, not_false_eq_true, ite_true]
        exact x12'
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


end Airbender.Blake2G.Proofs
