module
public import Proven.GKRProtocol.MemoryPortsNative.AddSubCached
public import Proven.GKRProtocol.MemoryPortsNative.JumpBranchCached
public import Proven.GKRProtocol.MemoryPortsNative.MulDivCached
public import Proven.GKRProtocol.MemoryPortsNative.ShiftBinopCached
public import Proven.GKRProtocol.MemoryPortsNative.SubwordMemoryCached
public import Proven.GKRProtocol.MemoryPortsNative.WordMemoryCached
public import Proven.GKRProtocol.MemoryPortsNative.UnifiedCached

@[expose] public section
namespace Airbender.Compiler.NativeMemory
set_option warningAsError true

/-- The PC-state token is injective, so exact token matching gives exact state matching. -/
theorem state_token_matching : StateTokenMatchingClaim := by
  intro before after matching
  simpa [List.map_map, Function.comp_def, state_token_left_inverse] using matching.map tokenState

/-- A one-state list matches its own tokens. -/
theorem state_token_matching_satisfiable : StateTokenMatchingSatisfiableClaim :=
  ⟨[⟨(0, 0), (0, 0)⟩], [⟨(0, 0), (0, 0)⟩], List.cons_ne_nil _ _, List.Perm.refl _⟩

end Airbender.Compiler.NativeMemory

namespace Airbender.Compiler
set_option warningAsError true

/-- Cached native gates, caches and product gates give the AddSub RAM outputs from the model tokens. -/
theorem addSub_cached_memory : AddSubCachedMemoryClaim := by
  intro E _ challenges physical values row family accepted placement extension
  obtain ⟨kind, assignment⟩ := row
  change kind = .addSub at family
  subst family
  exact MemoryPortsNative.AddSubCached.ram_products challenges physical values assignment accepted placement extension

/-- The canonical extension values of an arithmetic witness meet the AddSub memory premises. -/
theorem addSub_cached_memory_satisfiable : AddSubCachedMemorySatisfiableClaim := MemoryPortsNative.AddSubCached.satisfiable

/-- Cached native gates, caches and product gates give the JumpBranch RAM outputs from the model tokens. -/
theorem jumpBranch_cached_memory : JumpBranchCachedMemoryClaim := by
  intro E _ challenges physical values row family accepted placement extension
  obtain ⟨kind, assignment⟩ := row
  change kind = .jumpBranchSlt at family
  subst family
  exact MemoryPortsNative.JumpBranchCached.ram_products challenges physical values assignment accepted placement extension

/-- The canonical extension values of an arithmetic witness meet the JumpBranch memory premises. -/
theorem jumpBranch_cached_memory_satisfiable : JumpBranchCachedMemorySatisfiableClaim := MemoryPortsNative.JumpBranchCached.satisfiable

/-- Cached native gates, caches and product gates give the MulDiv RAM outputs from the model tokens. -/
theorem mulDiv_cached_memory : MulDivCachedMemoryClaim := by
  intro E _ challenges physical values row family accepted placement extension
  obtain ⟨kind, assignment⟩ := row
  change kind = .mulDiv at family
  subst family
  exact MemoryPortsNative.MulDivCached.ram_products challenges physical values assignment accepted placement extension

/-- The canonical extension values of an arithmetic witness meet the MulDiv memory premises. -/
theorem mulDiv_cached_memory_satisfiable : MulDivCachedMemorySatisfiableClaim := MemoryPortsNative.MulDivCached.satisfiable

/-- Cached native gates, caches and product gates give the ShiftBinop RAM outputs from the model tokens. -/
theorem shiftBinop_cached_memory : ShiftBinopCachedMemoryClaim := by
  intro E _ challenges physical values row family accepted placement extension
  obtain ⟨kind, assignment⟩ := row
  change kind = .shiftBinop at family
  subst family
  exact MemoryPortsNative.ShiftBinopCached.ram_products challenges physical values assignment accepted placement extension

/-- The canonical extension values of an arithmetic witness meet the ShiftBinop memory premises. -/
theorem shiftBinop_cached_memory_satisfiable : ShiftBinopCachedMemorySatisfiableClaim := MemoryPortsNative.ShiftBinopCached.satisfiable

/-- Cached native gates, caches and product gates give the SubwordMemory RAM outputs from the model tokens. -/
theorem subwordMemory_cached_memory : SubwordMemoryCachedMemoryClaim := by
  intro E _ challenges physical values row family accepted placement extension
  obtain ⟨kind, assignment⟩ := row
  change kind = .subwordMemory at family
  subst family
  exact MemoryPortsNative.SubwordMemoryCached.ram_products challenges physical values assignment accepted placement extension

/-- The canonical extension values of an arithmetic witness meet the SubwordMemory memory premises. -/
theorem subwordMemory_cached_memory_satisfiable : SubwordMemoryCachedMemorySatisfiableClaim := MemoryPortsNative.SubwordMemoryCached.satisfiable

/-- Cached native gates, caches and product gates give the WordMemory RAM outputs from the model tokens. -/
theorem wordMemory_cached_memory : WordMemoryCachedMemoryClaim := by
  intro E _ challenges physical values row family accepted placement extension
  obtain ⟨kind, assignment⟩ := row
  change kind = .wordMemory at family
  subst family
  exact MemoryPortsNative.WordMemoryCached.ram_products challenges physical values assignment accepted placement extension

/-- The canonical extension values of an arithmetic witness meet the WordMemory memory premises. -/
theorem wordMemory_cached_memory_satisfiable : WordMemoryCachedMemorySatisfiableClaim := MemoryPortsNative.WordMemoryCached.satisfiable

/-- Cached native gates, caches and product gates give the unified RAM outputs from the model tokens. -/
theorem unified_cached_memory : UnifiedCachedMemoryClaim := by
  intro E _ challenges physical values row accepted placement extension
  obtain ⟨kind, assignment⟩ := row
  cases kind
  exact MemoryPortsNative.UnifiedCached.ram_products challenges physical values assignment accepted placement extension

/-- The canonical extension values of an arithmetic witness meet the unified memory premises. -/
theorem unified_cached_memory_satisfiable : UnifiedCachedMemorySatisfiableClaim := MemoryPortsNative.UnifiedCached.satisfiable

end Airbender.Compiler
