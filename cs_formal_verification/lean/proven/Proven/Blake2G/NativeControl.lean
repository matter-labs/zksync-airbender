module
public import Proven.Blake2G.RVSpec

@[expose] public section
namespace Airbender.Blake2G.Proofs
set_option warningAsError true
open Arithmetic
set_option backward.isDefEq.respectTransparency false

/-- Bit seven selects the native G round count. -/
def nativeReduced (register : Fin 256) : Bool := decide (128 ≤ register.val)

/-- An out-of-schedule byte selects the first G operation. -/
def nativeIndex (register : Fin 256) : Nat :=
  if register.val % 128 < callCount (nativeReduced register) then register.val % 128 else 0

theorem native_index_bound (register : Fin 256) :
    nativeIndex register < callCount (nativeReduced register) := by
  unfold nativeIndex
  split_ifs with valid
  · exact valid
  · cases nativeReduced register <;> decide

/-- All byte controls select the scheduled G lanes, including the reset case. -/
theorem native_controller_offsets : ∀ register : Fin 256,
    (Control.step ⟨register, true⟩).stateOffsets =
      (Control.step (controllerAt (nativeReduced register) (nativeIndex register))).stateOffsets ∧
    (Control.step ⟨register, true⟩).messageOffsets =
      (Control.step (controllerAt (nativeReduced register) (nativeIndex register))).messageOffsets := by
  decide +kernel

/-- The native control table and the RV byte update agree for every byte. -/
theorem native_control_bits : ∀ register : Fin 256,
    (BitVec.ofNat 32 register.val).getLsbD 7 = nativeReduced register ∧
    ((BitVec.ofNat 32 register.val &&& 0x80#32) ||| BitVec.ofNat 32
      (if register.val % 128 + 1 < callCount (nativeReduced register)
        then register.val % 128 + 1 else 0)) = (Control.step ⟨register, true⟩).register.toBitVec := by
  decide +kernel


end Airbender.Blake2G.Proofs
