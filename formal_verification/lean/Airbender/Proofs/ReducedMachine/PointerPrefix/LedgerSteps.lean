import Airbender.Proofs.ReducedMachine.PointerPrefix.Data
import Airbender.Review.Trace.Families.ReducedMachine.PointerPrefix
import Airbender.Proofs.ReducedMachine.NativeMemoryTokens

namespace Airbender.NativePointerLedgerProofs
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
open Airbender.NativeMemoryTokens
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
abbrev F := ZMod mersenne31Modulus

def registerStateKey (count : Nat) (index : Fin 32) : MemoryKey :=
  ⟨⟨1,index.val,0⟩,
    #v[if count = 0 then 0 else if index.val = 11 then 128 else 0,0],
    #v[if count = 0 then 0 else if index.val = 0 then
      (if count ≤ 40 then 4 * count + 1 else 166 : Nat)
      else if index.val = 11 then 4 * min count 40 + 2 else 0,0]⟩

def registerState (count : Nat) :=
  (List.finRange 32).map (fun index => encodeKey (registerStateKey count index))

theorem gpr_step (row : Fin 41) :
    (registerState row.val ++ mainTokens (NativePointerPrefixProofs.assignment row) true).Perm
      (registerState (row.val + 1) ++ mainTokens (NativePointerPrefixProofs.assignment row) false) := by
  fin_cases row <;> decide +kernel

def pcState (count : Nat) : PCKey := ⟨#v[(4 * count : Nat),0],#v[(4 + 4 * count : Nat),0]⟩

theorem pc_step (row : Fin 41) :
    ([pcState row.val] ++ [ReducedMachine.NativeMainAuxiliary.mainPCKey (NativePointerPrefixProofs.assignment row) true]).Perm
      ([pcState (row.val + 1)] ++ [ReducedMachine.NativeMainAuxiliary.mainPCKey (NativePointerPrefixProofs.assignment row) false]) := by
  fin_cases row <;> decide +kernel

theorem initial_registers : registerState 0 = NativeInitializationSeedBoundary.initialRegisters := by
  rfl

theorem final_registers : registerState 41 =
    NativeInitializationSeedBoundary.finalRegisters NativePointerPrefix.prefixEndpoint := by decide +kernel

theorem initial_pc : pcState 0 = initialPCKey := by decide +kernel

theorem final_pc : pcState 41 = finalPCKey NativePointerPrefix.prefixEndpoint := by decide +kernel
end Airbender.NativePointerLedgerProofs
