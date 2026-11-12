module
public import Proven.Compiler.Lookups.Clean
public import Proven.Compiler.Lookups.NativeRanges
public import Proven.Compiler.Lookups.Source.JumpBranch
public import Proven.GKRProtocol.CleanArgumentsNative.JumpBranchCached

@[expose] public section
namespace Airbender.Compiler.NativeRangeLookups.JumpBranch
open Airbender Airbender.Compiler Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 65536

/-- Enabled source range tuples match complete independent native setup rows. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt)))
    (query : SourceLookupQuery) (member : query ∈ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries)
    (enabled : query.weight (RingHom.id _)
      ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .jumpBranchSlt) 1
      (query.fields.map (fun field => field.value
        ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement))) := by
  apply NativeSourceTransport.JumpBranch.source_member arithmetic arguments 1
    (query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘
      Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)) ?_ enabled
  simpa [NativeSourceTransport.JumpBranch.sourceRequests] using
    (List.mem_map.mpr ⟨query, member, rfl⟩ :
      query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ∈
        Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.map
          (fun entry => entry.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)))

theorem range_lookup0
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨0, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .jumpBranchSlt) 1 [Airbender.Compiler.LookupNative.JumpBranchCached.native.field4_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value0 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup1
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨1, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .jumpBranchSlt) 1 [Airbender.Compiler.LookupNative.JumpBranchCached.native.field5_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value1 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup2
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨2, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .jumpBranchSlt) 1 [Airbender.Compiler.LookupNative.JumpBranchCached.native.field6_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value2 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup3
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨3, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .jumpBranchSlt) 1 [Airbender.Compiler.LookupNative.JumpBranchCached.native.field7_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value3 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


end Airbender.Compiler.NativeRangeLookups.JumpBranch
