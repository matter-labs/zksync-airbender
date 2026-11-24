module
public import Proven.Compiler.Lookups.Clean
public import Proven.Compiler.Lookups.NativeRanges
public import Proven.Compiler.Lookups.Source.MulDiv
public import Proven.GKRProtocol.CleanArgumentsNative.MulDivCached

@[expose] public section
namespace Airbender.Compiler.NativeRangeLookups.MulDiv
open Airbender Airbender.Compiler Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 65536

/-- Enabled source range tuples match complete independent native setup rows. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv)))
    (query : SourceLookupQuery) (member : query ∈ Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries)
    (enabled : query.weight (RingHom.id _)
      ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 1
      (query.fields.map (fun field => field.value
        ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement))) := by
  apply NativeSourceTransport.MulDiv.source_member arithmetic arguments 1
    (query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘
      Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)) ?_ enabled
  simpa [NativeSourceTransport.MulDiv.sourceRequests] using
    (List.mem_map.mpr ⟨query, member, rfl⟩ :
      query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ∈
        Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.map
          (fun entry => entry.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)))

theorem range_lookup0
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨0, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 1 [Airbender.Compiler.LookupNative.MulDivCached.native.field8_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value0 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup1
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨1, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 1 [Airbender.Compiler.LookupNative.MulDivCached.native.field9_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value1 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup2
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨2, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 1 [Airbender.Compiler.LookupNative.MulDivCached.native.field10_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value2 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup3
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨3, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 1 [Airbender.Compiler.LookupNative.MulDivCached.native.field11_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value3 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup4
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨4, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 1 [Airbender.Compiler.LookupNative.MulDivCached.native.field12_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value4 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup5
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨5, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 1 [Airbender.Compiler.LookupNative.MulDivCached.native.field13_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value5 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup6
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression6).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨6, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 1 [Airbender.Compiler.LookupNative.MulDivCached.native.field14_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value6 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup7
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpression7).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.get ⟨7, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 1 [Airbender.Compiler.LookupNative.MulDivCached.native.field15_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.range_value7 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


end Airbender.Compiler.NativeRangeLookups.MulDiv
