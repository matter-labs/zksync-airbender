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

theorem pooled_arguments : UnrolledNativeArguments tables [] pooled workers := by
  refine ⟨workers_accepted, rfl, List.Perm.refl _, List.Perm.refl _, ?_⟩
  change (pooled.initialMemory ++ []).Perm (pooled.initialMemory ++ [])
  exact List.Perm.refl _

theorem unified_arguments : UnifiedNativeArguments tables [] unifiedTrace workers := by
  refine ⟨workers_accepted, rfl, List.Perm.refl _, List.Perm.refl _, ?_⟩
  change (unifiedTrace.initialMemory ++ []).Perm (unifiedTrace.initialMemory ++ [])
  exact List.Perm.refl _

end Airbender.NonVacuous.Machine

namespace Airbender.NonVacuous.Machine
open Airbender Trace Trace.Machine Arithmetic Compiler NativeArithmetic

theorem full_native : Native.UnrolledFullFromNativeSatisfiableClaim := by
  refine ⟨pooled, workers, zero, cells InitsTeardowns.importedLayout standaloneInits, [], standaloneInits,
    tables, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_, tables_bound, covers_rom, [], pooled_arguments⟩
  · exact boot .unrolledFullUnsigned _ _ (InitsTeardowns.Proofs.claims ⟨rfl, Or.inr rfl⟩) _ standalone_checked
  · intro entry member; cases member
  · intro entry member; cases member
  · intro row member; cases member

theorem reduced_native : Native.UnrolledReducedFromNativeSatisfiableClaim := by
  refine ⟨pooled, workers, zero, cells InitsTeardowns.importedLayout standaloneInits, [], standaloneInits,
    tables, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, tables_bound, covers_rom, [], pooled_arguments⟩
  · exact boot .unrolledReduced _ _ (InitsTeardowns.Proofs.claims ⟨rfl, Or.inr rfl⟩) _ standalone_checked
  · intro row member; cases member

theorem unified_native : Native.UnifiedFromNativeSatisfiableClaim := by
  refine ⟨unifiedTrace, workers, zero, cells InitsTeardowns.unifiedLayout unifiedInits, [], unifiedInits,
    tables, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_, tables_bound, [], unified_arguments⟩
  · exact boot .unified _ _ (InitsTeardowns.Proofs.claims ⟨rfl, Or.inl rfl⟩) _ unified_checked
  · intro entry member; cases member
  · intro row member; cases member
end Airbender.NonVacuous.Machine
