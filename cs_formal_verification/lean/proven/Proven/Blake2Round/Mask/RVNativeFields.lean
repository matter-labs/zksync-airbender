module
public import Proven.Blake2Round.Mask.RVPhysical

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic Trace Trace.Proofs Delegation.Proofs Blake2Round.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A native register port supplies its actual values at the history endpoints. -/
theorem rv_register_port {w : Nat → ZMod babyBearModulus} {before after : RV.State}
    {index : BitVec 5} (i : Fin 43)
    (address : importedConstraintsMemoryPorts[i.val].address.code w = (Cell.register index).addressCode)
    (ports : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w))) :
    before.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].readCode w) ∧
      after.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].writeCode w) := by
  obtain ⟨cell, code, readBefore, readAfter⟩ :=
    ports importedConstraintsMemoryPorts[i.val] (Array.getElem_mem (by change i.val < 43; omega))
  have same : cell = .register index := cell_address_injective (code.trans address)
  subst same
  rw [readRV_register] at readBefore readAfter
  exact ⟨Option.some.inj readBefore, Option.some.inj readAfter⟩

/-- A native state pointer retains its 128-byte low-limb alignment in the RV encoding. -/
theorem pointer_aligned_128 {word : Word} (bounded : word.Bounded) (aligned : word.lo % 128 = 0) :
    word.toBitVec.toNat % 128 = 0 := by
  rw [Word.toBitVec_toNat bounded]
  change (word.lo + 65536 * word.hi) % 128 = 0
  omega

/-- A native message pointer retains its 64-byte low-limb alignment in the RV encoding. -/
theorem pointer_aligned_64 {word : Word} (bounded : word.Bounded) (aligned : word.lo % 64 = 0) :
    word.toBitVec.toNat % 64 = 0 := by
  rw [Word.toBitVec_toNat bounded]
  change (word.lo + 65536 * word.hi) % 64 = 0
  omega

end Airbender.Blake2Round.Mask.Proofs
