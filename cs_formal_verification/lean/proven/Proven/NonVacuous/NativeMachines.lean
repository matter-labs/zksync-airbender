module
public import Proven.NonVacuous.MachineBoot

@[expose] public section
namespace Airbender.NonVacuous.Machine
open Airbender Trace Trace.Machine Arithmetic Compiler NativeArithmetic

def standaloneInits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout) :=
  [⟨#v[0, 1, 2, 3, 4, 5, 6, 7], fun _ _ => 0⟩]

def unifiedInits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout) :=
  [⟨#v[0, 1], fun _ _ => 0⟩]

theorem standalone_checked : InitsTeardowns.TopBitsChecked (standaloneInits.flatMap fun w => w.topBits.toList) := by
  change InitsTeardowns.TopBitsChecked (List.range 8)
  refine ⟨List.pairwise_lt_range, ?_⟩
  intro top member
  have bounded := List.mem_range.mp member
  change top < 64
  omega

theorem unified_checked : InitsTeardowns.TopBitsChecked (unifiedInits.flatMap fun w => w.topBits.toList) := by
  change InitsTeardowns.TopBitsChecked (List.range 2)
  refine ⟨List.pairwise_lt_range, ?_⟩
  intro top member
  have bounded := List.mem_range.mp member
  change top < 64
  omega

noncomputable def workers : WorkerPools babyBearModulus where
  standard := ⟨Delegation.modeledSetup Keccak.Controller.rows, [], [], []⟩
  split := ⟨[], [], []⟩

theorem workers_accepted : WorkersAccepted workers := by
  constructor <;> intro row member <;> cases member

noncomputable def tables := NativePublicSetup.rows zero []

theorem tables_bound : NativePublicSetup.Bound zero [] tables := by
  constructor
  · rfl
  · decide +kernel
  · intro entry member; cases member
  · intro entry member; cases member

noncomputable def pooled : PooledTrace babyBearModulus :=
  emptyTrace (⟨ROM.table (cells InitsTeardowns.importedLayout standaloneInits)
      (romImageRV zero (cells InitsTeardowns.importedLayout standaloneInits)),
    Verification.subwordTable (ROM.wordsRV zero)⟩ : PooledSetup babyBearModulus)
    InitsTeardowns.importedLayout standaloneInits

noncomputable def unifiedTrace : UnifiedTrace babyBearModulus :=
  emptyTrace (UnifiedReduced.Setup.tableRV zero) InitsTeardowns.unifiedLayout unifiedInits

theorem covers_rom : NativePublicSetup.CoversROM (cells InitsTeardowns.importedLayout standaloneInits) := by
  intro index
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨0, by decide +kernel, List.mem_map.mpr ⟨index.val, ?_, ?_⟩⟩
  · change index.val ∈ List.range 16777216
    rw [List.mem_range]
    have bounded := index.isLt
    omega
  · have address : InitsTeardowns.windowAddress InitsTeardowns.importedLayout 0 index.val = 4 * index.val := by
      rw [InitsTeardowns.windowAddress,
        show InitsTeardowns.importedLayout.wordBits = 2 from rfl,
        show InitsTeardowns.importedLayout.traceLog = 24 from rfl]
      simp [Nat.mul_comm]
    exact congrArg (fun address => Cell.ram (BitVec.ofNat 32 address)) address

/-- The zero standalone teardown columns retain every public seed token. -/
theorem pooled_memory : pooled.initialMemory.Perm pooled.terminalMemory := by
  have tokens : standaloneInits.flatMap InitsTeardowns.Witness.teardownTokens =
      standaloneInits.flatMap InitsTeardowns.Witness.initTokens := by
    simp only [standaloneInits, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact InitsTeardowns.Proofs.teardown_zero _ (fun _ _ => rfl)
  change (registerSeeds ++ standaloneInits.flatMap InitsTeardowns.Witness.initTokens).Perm
    (registerSeeds ++ standaloneInits.flatMap InitsTeardowns.Witness.teardownTokens)
  rw [tokens]

/-- The zero unified teardown columns retain every public seed token. -/
theorem unified_memory : unifiedTrace.initialMemory.Perm unifiedTrace.terminalMemory := by
  have tokens : unifiedInits.flatMap InitsTeardowns.Witness.teardownTokens =
      unifiedInits.flatMap InitsTeardowns.Witness.initTokens := by
    simp only [unifiedInits, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact InitsTeardowns.Proofs.teardown_zero _ (fun _ _ => rfl)
  change (registerSeeds ++ unifiedInits.flatMap InitsTeardowns.Witness.initTokens).Perm
    (registerSeeds ++ unifiedInits.flatMap InitsTeardowns.Witness.teardownTokens)
  rw [tokens]

theorem pooled_arguments : UnrolledNativeArguments tables [] pooled workers := by
  refine ⟨⟨[], rfl, rfl⟩, rfl, List.Perm.refl _, List.Perm.refl _, ?_⟩
  change (pooled.initialMemory ++ []).Perm (pooled.terminalMemory ++ [])
  simpa only [List.append_nil] using pooled_memory

theorem unified_arguments : UnifiedNativeArguments tables [] unifiedTrace workers := by
  refine ⟨⟨[], rfl, rfl⟩, rfl, List.Perm.refl _, List.Perm.refl _, ?_⟩
  change (unifiedTrace.initialMemory ++ []).Perm (unifiedTrace.terminalMemory ++ [])
  simpa only [List.append_nil] using unified_memory

end Airbender.NonVacuous.Machine
