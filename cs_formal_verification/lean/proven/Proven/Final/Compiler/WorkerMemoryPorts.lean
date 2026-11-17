module
public import Proven.GKRProtocol.WorkerPortsNative.BigintCachedWitness

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

end Airbender.Compiler
