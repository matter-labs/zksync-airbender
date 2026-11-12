module
public import Proven.Blake2G.RVNativeCallLink
public import Proven.Blake2G.Memory

@[expose] public section
namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option backward.isDefEq.respectTransparency false

/-- An active native controller row reads an eight-bit control word. -/
theorem native_control_bound {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (active : w Variables.execute = 1) (readBound : (w Variables.controlReadLo).val < 65536) :
    (w Variables.controlReadLo).val < 256 := by
  obtain ⟨key, encoded, _⟩ := Control.Proofs.control_columns (by decide) core
  change w 3 + 256 * w 0 = (key.val : ZMod babyBearModulus) at encoded
  change w 0 = 1 at active
  rw [active, mul_one] at encoded
  have values := congrArg ZMod.val encoded
  rw [ZMod.val_add, ZMod.val_natCast] at values
  have small : (w 3).val + 256 < babyBearModulus := by
    change (w 3).val < 65536 at readBound
    unfold babyBearModulus
    omega
  norm_num only [show (256 : ZMod babyBearModulus).val = 256 by decide] at values
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by have := key.isLt; unfold babyBearModulus; omega)] at values
  change (w 3).val < 256
  have := key.isLt
  omega

/-- A native G register port supplies its actual values at the history endpoints. -/
theorem rv_native_register_port {w : Nat → ZMod p} {before after : RV.State}
    {index : BitVec 5} (i : Fin 9)
    (address : importedConstraintsMemoryPorts[i.val].address.code w = (Cell.register index).addressCode)
    (ports : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w))) :
    before.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].readCode w) ∧
      after.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].writeCode w) := by
  obtain ⟨cell, code, readBefore, readAfter⟩ :=
    ports importedConstraintsMemoryPorts[i.val] (Array.getElem_mem (by change i.val < 9; omega))
  have same : cell = .register index := cell_address_injective (code.trans address)
  subst same
  rw [readRV_register] at readBefore readAfter
  exact ⟨Option.some.inj readBefore, Option.some.inj readAfter⟩

/-- A native pointer word retains its low-limb alignment in the RV encoding. -/
theorem native_pointer_aligned {word : Word} (bounded : word.Bounded) (aligned : word.lo % 64 = 0) :
    word.toBitVec.toNat % 64 = 0 := by
  rw [Word.toBitVec_toNat bounded]
  change (word.lo + 65536 * word.hi) % 64 = 0
  omega

end Airbender.Blake2G.Proofs
