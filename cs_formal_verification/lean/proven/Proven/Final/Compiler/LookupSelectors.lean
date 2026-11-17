module
public import Proven.KernelExact
public import Proven.Compiler.Lookups.Selectors.Pooled
public import Proven.Compiler.Lookups.Selectors.Unified
public import Proven.Compiler.Lookups.Selectors.Introduction
public import Proven.Compiler.Lookups.Tables

@[expose] public section
namespace Airbender.Compiler.NativeLookups
set_option maxRecDepth 32768

/-- Every cached CPU query operand has its actual native selector and expansion path. -/
theorem cached_lookup_selectors : CachedLookupSelectorsClaim := by
  intro family
  have tables := Proofs.Tables.cpu family
  cases family with
  | pooled family =>
      obtain ⟨covered, resolved, grouped⟩ := Proofs.Pooled.binding family
      exact ⟨covered, resolved, grouped, tables⟩
  | unified =>
      obtain ⟨covered, resolved, grouped⟩ := Proofs.Unified.binding
      exact ⟨covered, resolved, grouped, tables⟩

/-- The selector conditions hold for a nonempty native query list. -/
theorem cached_lookup_selectors_satisfiable : CachedLookupSelectorsSatisfiableClaim :=
  Proofs.Introduction.satisfiable

end Airbender.Compiler.NativeLookups
