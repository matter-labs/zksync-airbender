import Airbender.Review.Circuits.ReducedMachine.InitializationSeedBoundaryTheorems
import Tests.NativeInitializationBatch

namespace Airbender.Tests.NativeInitializationSeedBoundary
open Airbender.NativeInitializationSeedBoundary Airbender.NativeInitializationSeedBoundaryProofs
open Airbender.NativeInitializationBatch (Proof mainProofs)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem all32_register_seeds : initialRegisters.length = 32 ∧ registerCells.length = 32 := by
  simp [initialRegisters,registerCells]

theorem x0_seed : initialRegisters[0]'(by decide +kernel) = (Trace.Cell.register 0).initialToken 0 := by
  exact initial_register 0

theorem x31_seed : initialRegisters[31]'(by decide +kernel) = (Trace.Cell.register 31).initialToken 0 := by
  exact initial_register 31

private def inputs : PublicBoundary := ⟨fun _ => ⟨0,#v[700000,17]⟩,0,#v[4,0]⟩

theorem final_x0_time_retained : ((finalRegisters inputs)[0]'(by decide +kernel)).time = (700000,17) := rfl

theorem public_projection_both_sides (write : Bool) :
    (Airbender.NativeTokenLedger.publicTokens inputs write).filterMap Airbender.NativeTokenLedger.memoryProjection =
      if write then initialRegisters else finalRegisters inputs := public_projection inputs write

theorem register_cells_unique : registerCells.Nodup := register_domain

theorem all_registers_architectural : architecturalCells registerCells = registerCells := by
  apply List.filter_eq_self.mpr
  intro c member
  obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
  exact Airbender.ReducedMachine.NativeShadowProofs.architectural_register _

theorem zero_is_shadow : shadowSeed (.ram 0) = some (0,0) := by decide +kernel

theorem last_shadow_byte : shadowSeed (.ram (BitVec.ofNat 32 4194303)) = some (BitVec.ofNat 32 4194303,0) := by decide +kernel

theorem first_architectural_ram : shadowSeed (.ram (BitVec.ofNat 32 4194304)) = none ∧
    Airbender.ReducedMachine.NativeShadow.architecturalAddress (Trace.Cell.ram (BitVec.ofNat 32 4194304)).addressCode = true := by
  constructor
  · decide +kernel
  · rw [Airbender.ReducedMachine.NativeShadowProofs.architectural_ram]; decide +kernel

/-- PURE partition control, not a full accepted nonempty circuit witness. -/
theorem shadow_duplicates_preserved : (shadowSeeds [Trace.Cell.ram 16,Trace.Cell.ram 16]).length = 2 := by decide +kernel

theorem actual_shadow_tokens_are_zero :
    Airbender.ReducedMachine.NativeShadow.shadowTokens (p := mersenne31Modulus) (shadowSeeds [Trace.Cell.ram 16]) =
      [(Trace.Cell.ram 16).initialToken 0] := by decide +kernel

theorem zero_shadow_not_rom_value : (Trace.Cell.ram 16).initialToken (p := mersenne31Modulus) 0 ≠
    (Trace.Cell.ram 16).initialToken (BitVec.ofNat 32 21015) := by decide +kernel

theorem mixed_domain_partition :
    [Trace.Cell.register 0,Trace.Cell.ram 16,Trace.Cell.ram (BitVec.ofNat 32 4194304)].Perm
      (architecturalCells [Trace.Cell.register 0,Trace.Cell.ram 16,Trace.Cell.ram (BitVec.ofNat 32 4194304)] ++
        (shadowSeeds [Trace.Cell.register 0,Trace.Cell.ram 16,Trace.Cell.ram (BitVec.ofNat 32 4194304)]).map fun seed => Trace.Cell.ram seed.1) :=
  cell_partition _

theorem generic_projection_duplicates : ([0,0] : List Nat).Perm [0,0] := by
  exact projection_balance id some [0,0] [0] [] [] [] [0] [] [0]
    (by intro values; simp) rfl rfl (by rfl)

theorem complete_empty_boundary : Effects ([] : List (Proof F)) :=
  native_complete_seed_boundary _ _ _ _ _ _ Airbender.Tests.NativeInitializationBatch.empty_combined_component

theorem complete_conditional_boundary {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {publicInputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch publicInputs inverse) :
    Effects proofs := native_complete_seed_boundary embed memory ch pc gamma config accepted

theorem complete_conditional_memory {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {publicInputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch publicInputs inverse) :
    (initialTokens proofs ++ accessTokens proofs batch true).Perm
      (terminalTokens proofs publicInputs ++ accessTokens proofs batch false) :=
  native_complete_memory_matching embed memory ch pc gamma config accepted

end Airbender.Tests.NativeInitializationSeedBoundary
