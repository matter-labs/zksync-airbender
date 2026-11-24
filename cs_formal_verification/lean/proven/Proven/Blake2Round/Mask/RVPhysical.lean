module
public import Proven.Blake2Round.Mask.Native
public import Proven.Blake2Round.RVPhysical

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic Trace Trace.Proofs Delegation.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The arbitrary-mask interface reads the same native words as the scheduled interface. -/
theorem native_word_views (w : Nat → ZMod babyBearModulus) :
    (inputOf w).state = (Native.input 0 w).state ∧
    (inputOf w).extended = (Native.input 0 w).extended ∧
    (inputOf w).message = (Native.input 0 w).message ∧
    (outputOf w).state = (Native.output w).state ∧
    (outputOf w).extended = (Native.output w).extended := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Existing native port transport recovers both physical state blocks for every mask. -/
theorem rv_physical_words {w : Nat → ZMod babyBearModulus} {before after : RV.State}
    {state message : RV.Word}
    (addresses : Addresses.spec ⟨(inputOf w).statePointer, (inputOf w).messagePointer⟩ (outputOf w).addresses)
    (pointers : (inputOf w).statePointer = Word.ofBitVec state ∧
      (inputOf w).messagePointer = Word.ofBitVec message)
    (reads : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports,
      ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w))) :
    (inputOf w).state = (Blake2Round.Proofs.rvPhysicalState before state).1 ∧
    (inputOf w).extended = (Blake2Round.Proofs.rvPhysicalState before state).2 ∧
    (inputOf w).message = rvBlockWords before message 16 0 ∧
    (outputOf w).state = (Blake2Round.Proofs.rvPhysicalState after state).1 ∧
    (outputOf w).extended = (Blake2Round.Proofs.rvPhysicalState after state).2 ∧
    rvBlockWords before message 16 0 = rvBlockWords after message 16 0 := by
  have observations := Blake2Round.Proofs.rv_round_word_observations (round := 0)
    (before := before) (after := after) addresses pointers reads writes observed
  obtain ⟨stateRead, extendedRead, messageRead, stateWrite, extendedWrite, unchanged⟩ :=
    Blake2Round.Proofs.rv_physical_row_words 0 observations
  have views := native_word_views w
  exact ⟨views.1.trans stateRead, views.2.1.trans extendedRead, views.2.2.1.trans messageRead,
    views.2.2.2.1.trans stateWrite, views.2.2.2.2.trans extendedWrite, unchanged⟩

end Airbender.Blake2Round.Mask.Proofs
