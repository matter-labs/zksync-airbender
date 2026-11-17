module
public import Proven.GKRProtocol.WorkerPortsNative.BigintCachedWitness
public import Proven.GKRProtocol.WorkerPortsNative.BlakeGCachedWitness

@[expose] public section
namespace Airbender.Compiler
set_option warningAsError true

/-- Cached native gates, caches and product gates give the bigint RAM outputs from the model tokens. -/
theorem bigint_cached_memory : BigintCachedMemoryClaim := by
  intro E _ challenges physical values row selected accepted placement extension
  obtain ⟨kind, assignment⟩ := row
  change kind = .bigint at selected
  subst selected
  exact WorkerPortsNative.BigintCached.ram_products challenges physical values assignment accepted placement extension

/-- The program values of an arithmetic witness meet the bigint memory premises. -/
theorem bigint_cached_memory_satisfiable : BigintCachedMemorySatisfiableClaim :=
  WorkerPortsNative.BigintCached.satisfiable

/-- Cached native gates, caches and product gates give the BLAKE2 G RAM outputs from the model tokens. -/
theorem blakeG_cached_memory : BlakeGCachedMemoryClaim := by
  intro E _ challenges physical values row selected accepted placement extension
  obtain ⟨kind, assignment⟩ := row
  change kind = .blakeG at selected
  subst selected
  exact WorkerPortsNative.BlakeGCached.ram_products challenges physical values assignment accepted placement extension

/-- The program values of an arithmetic witness meet the BLAKE2 G memory premises. -/
theorem blakeG_cached_memory_satisfiable : BlakeGCachedMemorySatisfiableClaim :=
  WorkerPortsNative.BlakeGCached.satisfiable

end Airbender.Compiler
