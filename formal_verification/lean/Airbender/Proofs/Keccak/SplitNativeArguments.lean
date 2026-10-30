import Airbender.Proofs.Keccak.SplitNativeRAMDomain

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Derived native input facts for one blessed split call. They contain only
its input control and pointer. No output, memory effect or execution is stored. -/
def nativeCallArguments (cached : Bool) (row : Row babyBearModulus) : Prop :=
  ∃ index : Fin 361,
    (readToken row.assignment (nativeRegisterPort cached row 0)).word.toBitVec = BitVec.ofNat 32 (controlAt index.val) ∧
    (readToken row.assignment (nativeRegisterPort cached row 1)).word.Bounded ∧
    ROM.limit ≤ (readToken row.assignment (nativeRegisterPort cached row 1)).word.toBitVec.toNat ∧
    (readToken row.assignment (nativeRegisterPort cached row 1)).word.toBitVec.toNat % 256 = 0

private theorem register_read (cached : Bool) (row : Row babyBearModulus) (index : Fin 2)
    (before : State)
    (observed : ∃ cell : Cell, cell.addressCode = (nativeRegisterPort cached row index).address.code row.assignment ∧
      cell.read before = .ok (readToken row.assignment (nativeRegisterPort cached row index)).word.toBitVec before) :
    (Cell.register (BitVec.ofNat 5 (10 + index.val))).read before =
      .ok (readToken row.assignment (nativeRegisterPort cached row index)).word.toBitVec before := by
  obtain ⟨cell, address, read⟩ := observed
  have code : (nativeRegisterPort cached row index).address.code row.assignment =
      (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode := by
    rw [native_register_port_address]
    fin_cases index <;> rfl
  have same := cell_address_injective (address.trans code)
  exact same ▸ read

/-- Actual reference register reads determine state-independent native inputs. -/
theorem native_arguments_of_reference (cached : Bool) (row : Row babyBearModulus)
    (index : Fin 361) (before : State) (arguments : ArgumentsAt index.val before)
    (pointerBound : (readToken row.assignment (nativeRegisterPort cached row 1)).word.Bounded)
    (registers : ∀ register : Fin 2, ∃ cell : Cell,
      cell.addressCode = (nativeRegisterPort cached row register).address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment (nativeRegisterPort cached row register)).word.toBitVec before) :
    nativeCallArguments cached row := by
  obtain ⟨control, pointer, readControl, readPointer, selected, outside, aligned⟩ := arguments
  have controlRead := register_read cached row 0 before (registers 0)
  have pointerRead := register_read cached row 1 before (registers 1)
  have controlEqual := (EStateM.Result.ok.inj (controlRead.symm.trans readControl)).1
  have pointerEqual := (EStateM.Result.ok.inj (pointerRead.symm.trans readPointer)).1
  refine ⟨index, controlEqual.trans selected, pointerBound, ?_, ?_⟩
  · rw [pointerEqual]
    exact outside
  · rw [pointerEqual]
    exact aligned

/-- The same actual input tokens recover the public split arguments at any
history cut that observes them. Native input facts contain no state result. -/
theorem native_arguments_at_observations (cached : Bool) (row : Row babyBearModulus)
    (arguments : nativeCallArguments cached row) (before : State)
    (registers : ∀ register : Fin 2, ∃ cell : Cell,
      cell.addressCode = (nativeRegisterPort cached row register).address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment (nativeRegisterPort cached row register)).word.toBitVec before) :
    ∃ index : Fin 361, ArgumentsAt index.val before := by
  obtain ⟨index, selected, _, outside, aligned⟩ := arguments
  exact ⟨index, _, _, register_read cached row 0 before (registers 0),
    register_read cached row 1 before (registers 1), selected, outside, aligned⟩

end Airbender.Keccak.Split.Native.Proofs
