module
public import Proven.Compiler.Lookups.Clean
public import Proven.Compiler.Lookups.NativeRanges
public import Proven.Compiler.Lookups.Source.ShiftBinop
public import Proven.GKRProtocol.CleanArgumentsNative.ShiftBinopCached

@[expose] public section
namespace Airbender.Compiler.NativeRangeLookups.ShiftBinop
open Airbender Airbender.Compiler Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 65536

/-- Enabled source range tuples match complete independent native setup rows. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .shiftBinop))
      (NativeLookups.selectorsFor (.pooled .shiftBinop)) physical (NativePublicSetup.rows initial program (.pooled .shiftBinop)))
    (query : SourceLookupQuery) (member : query ∈ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries)
    (enabled : query.weight (RingHom.id _)
      ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .shiftBinop) 1
      (query.fields.map (fun field => field.value
        ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))) := by
  apply NativeSourceTransport.ShiftBinop.source_member arithmetic arguments 1
    (query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘
      Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)) ?_ enabled
  simpa [NativeSourceTransport.ShiftBinop.sourceRequests] using
    (List.mem_map.mpr ⟨query, member, rfl⟩ :
      query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ∈
        Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries.map
          (fun entry => entry.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)))

theorem range_lookup0
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .shiftBinop))
      (NativeLookups.selectorsFor (.pooled .shiftBinop)) physical (NativePublicSetup.rows initial program (.pooled .shiftBinop))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries.get ⟨0, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .shiftBinop) 1 [Airbender.Compiler.LookupNative.ShiftBinopCached.native.field5_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.range_value0 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


theorem range_lookup1
    (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .shiftBinop))
      (NativeLookups.selectorsFor (.pooled .shiftBinop)) physical (NativePublicSetup.rows initial program (.pooled .shiftBinop))) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries.get ⟨1, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : NativePublicSetup.Proofs.Contains initial program (.pooled .shiftBinop) 1 [Airbender.Compiler.LookupNative.ShiftBinopCached.native.field6_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.range_value1 physical data arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact NativePublicSetup.Proofs.range16_clean_refinement _ valid _


end Airbender.Compiler.NativeRangeLookups.ShiftBinop
