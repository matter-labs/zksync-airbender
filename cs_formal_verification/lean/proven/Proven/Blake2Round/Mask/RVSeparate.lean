module
public import Proven.Blake2Round.Mask.RVNativeFields

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic Trace Trace.Proofs Delegation.Proofs Blake2Round.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Distinct native RAM accesses exclude equal round state and message pointers. -/
theorem native_pointer_separate {w : Nat → ZMod babyBearModulus} {state message : RV.Word}
    (addresses : ∀ i : Fin 40, importedConstraintsIndirectPorts[i].address w =
      if i.val < 24 then state + BitVec.ofNat 32 (4 * i.val)
      else message + BitVec.ofNat 32 (4 * (i.val - 24)))
    (observed : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w)
    (distinct : ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).memorySteps.map fun edge => edge.1.address).Nodup) :
    state ≠ message := by
  intro same
  obtain ⟨one, oneCode⟩ := observed importedConstraintsMemoryPorts[1]
    (Array.getElem_mem (by change 1 < 43; decide))
  obtain ⟨two, twoCode⟩ := observed importedConstraintsMemoryPorts[26]
    (Array.getElem_mem (by change 26 < 43; decide))
  have oneCell := indirect_cell (show one.addressCode =
    (MemoryAddress.indirect importedConstraintsIndirectPorts[0]).code w from oneCode)
  have twoCell := indirect_cell (show two.addressCode =
    (MemoryAddress.indirect importedConstraintsIndirectPorts[24]).code w from twoCode)
  have stateAddress := addresses 0
  have messageAddress := addresses 24
  simp only [Fin.getElem_fin, Fin.val_zero, show ((24 : Fin 40) : Nat) = 24 from rfl] at stateAddress messageAddress
  rw [stateAddress] at oneCell
  rw [messageAddress] at twoCell
  have equalCells : one = two := by
    rw [oneCell, twoCell, same]
    simp
  subst equalCells
  have equal := oneCode.symm.trans twoCode
  have samePorts :
      ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).memorySteps.map fun edge => edge.1.address)[1]'
        (by change 1 < 43; decide) =
      ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).memorySteps.map fun edge => edge.1.address)[26]'
        (by change 26 < 43; decide) := by
    simpa [Delegation.Row.memorySteps, Delegation.Row.ports, importedConstraintsMemoryPorts, readToken] using equal
  have impossible := distinct.getElem_inj_iff.mp samePorts
  omega

end Airbender.Blake2Round.Mask.Proofs
