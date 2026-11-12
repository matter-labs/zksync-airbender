module
public import Proven.Compiler.Lookups.Clean
public import Proven.Compiler.Lookups.NativeRanges
public import Proven.Compiler.Lookups.Source.MulDiv
public import Proven.GKRProtocol.CleanGenericArgumentsNative.MulDivCached
public import Proven.Compiler.PrimitiveMembership
public import Proven.Compiler.Lookups.Pairs
public import Proven.Constraints

@[expose] public section
namespace Airbender.Compiler.NativeVectorLookups.MulDiv
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
    (query : SourceLookupQuery) (member : query ∈ Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries)
    (enabled : query.weight (RingHom.id _)
      ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 0
      (query.fields.map (fun field => field.value
        ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement))) := by
  apply NativeSourceTransport.MulDiv.source_member arithmetic arguments 0
    (query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘
      Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)) ?_ enabled
  simpa [NativeSourceTransport.MulDiv.sourceRequests] using
    (List.mem_map.mpr ⟨query, member, rfl⟩ :
      query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ∈
        Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.map
          (fun entry => entry.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)))

noncomputable def fixedLookup0 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.regIsZeroTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression0_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression0_1

noncomputable def fixedLookup1 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16LowByteTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression1_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression1_1

noncomputable def fixedLookup2 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16LowByteTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression2_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression2_1

noncomputable def fixedLookup3 : Lookup Source.BaseField :=
  Verification.range13 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression3_0

noncomputable def fixedLookup4 : Lookup Source.BaseField :=
  Verification.range13 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression4_0

noncomputable def fixedLookup5 : Lookup Source.BaseField :=
  Verification.range13 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression5_0

noncomputable def fixedLookup6 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16LowByteTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression6_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression6_1

noncomputable def fixedLookup7 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16LowByteTable Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression7_0 Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.genericExpression7_1

noncomputable def fixedLookups : List (Lookup Source.BaseField) := [fixedLookup0, fixedLookup1, fixedLookup2, fixedLookup3, fixedLookup4, fixedLookup5, fixedLookup6, fixedLookup7]

theorem generic_lookup0
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    fixedLookup0.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨0, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (1 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) = 1 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field0_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value0_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field0_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value0_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact NativePrimitiveMembership.MulDiv.tag1_contains initial program setupRow selected _

theorem generic_lookup1
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    fixedLookup1.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨1, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) = 41 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field1_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value1_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field1_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value1_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact NativePrimitiveMembership.MulDiv.tag41_contains initial program setupRow selected _

theorem generic_lookup2
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    fixedLookup2.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨2, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) = 41 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field2_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value2_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field2_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value2_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact NativePrimitiveMembership.MulDiv.tag41_contains initial program setupRow selected _

theorem generic_lookup3
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    fixedLookup3.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨3, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (26 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) = 26 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field3_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value3_0 physical data arithmetic).trans sourceCell0
  apply Verification.range13_contains
  rw [same0]
  exact NativePrimitiveMembership.MulDiv.tag26_contains initial program setupRow selected

theorem generic_lookup4
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    fixedLookup4.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨4, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (26 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) = 26 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field4_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value4_0 physical data arithmetic).trans sourceCell0
  apply Verification.range13_contains
  rw [same0]
  exact NativePrimitiveMembership.MulDiv.tag26_contains initial program setupRow selected

theorem generic_lookup5
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    fixedLookup5.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨5, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (26 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) = 26 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field5_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value5_0 physical data arithmetic).trans sourceCell0
  apply Verification.range13_contains
  rw [same0]
  exact NativePrimitiveMembership.MulDiv.tag26_contains initial program setupRow selected

theorem generic_lookup6
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    fixedLookup6.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨6, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) = 41 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field6_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value6_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field6_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value6_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact NativePrimitiveMembership.MulDiv.tag41_contains initial program setupRow selected _

theorem generic_lookup7
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    fixedLookup7.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.get ⟨7, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 8) = 41 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field7_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value7_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivCached.native.field7_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .mulDiv) setupRow 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native.part0.generic_value7_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact NativePrimitiveMembership.MulDiv.tag41_contains initial program setupRow selected _

end Airbender.Compiler.NativeVectorLookups.MulDiv
