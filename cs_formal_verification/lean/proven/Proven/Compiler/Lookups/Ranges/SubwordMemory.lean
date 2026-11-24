module
public import Proven.Compiler.Lookups.Clean
public import Proven.Compiler.Lookups.NativeRanges
public import Proven.Compiler.Lookups.Source.SubwordMemory
public import Proven.GKRProtocol.CleanArgumentsNative.SubwordMemoryCached

@[expose] public section
namespace Airbender.Compiler.NativeRangeLookups.SubwordMemory
open Airbender Airbender.Compiler Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 65536

/-- Enabled source range tuples match complete independent native setup rows. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory)))
    (query : SourceLookupQuery) (member : query ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries)
    (enabled : query.weight (RingHom.id _)
      ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 1
      (query.fields.map (fun field => field.value
        ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement))) := by
  apply NativeSourceTransport.SubwordMemory.source_member arithmetic arguments 1
    (query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘
      Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)) ?_ enabled
  simpa [NativeSourceTransport.SubwordMemory.sourceRequests] using
    (List.mem_map.mpr ⟨query, member, rfl⟩ :
      query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ∈
        Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.map
          (fun entry => entry.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)))

theorem range_lookup0
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.get ⟨0, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 1 [Airbender.Compiler.LookupNative.SubwordMemoryCached.native.field2_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.range_value0 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup1
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.get ⟨1, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 1 [Airbender.Compiler.LookupNative.SubwordMemoryCached.native.field3_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.range_value1 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup2
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.get ⟨2, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 1 [Airbender.Compiler.LookupNative.SubwordMemoryCached.native.field4_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.range_value2 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup3
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.get ⟨3, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 1 [Airbender.Compiler.LookupNative.SubwordMemoryCached.native.field5_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.range_value3 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup4
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.get ⟨4, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 1 [Airbender.Compiler.LookupNative.SubwordMemoryCached.native.field6_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.range_value4 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


end Airbender.Compiler.NativeRangeLookups.SubwordMemory
