module
public import Proven.Compiler.Lookups.Clean
public import Proven.Compiler.Lookups.NativeRanges
public import Proven.Compiler.Lookups.Source.JumpBranch
public import Proven.GKRProtocol.CleanGenericArgumentsNative.JumpBranchCached
public import Proven.Compiler.PrimitiveMembership
public import Proven.Compiler.Lookups.Pairs

@[expose] public section
namespace Airbender.Compiler.NativeVectorLookups.JumpBranch
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
    (query : SourceLookupQuery) (member : query ∈ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries)
    (enabled : query.weight (RingHom.id _)
      ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .jumpBranchSlt) 0
      (query.fields.map (fun field => field.value
        ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement))) := by
  apply NativeSourceTransport.JumpBranch.source_member arithmetic arguments 0
    (query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘
      Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)) ?_ enabled
  simpa [NativeSourceTransport.JumpBranch.sourceRequests] using
    (List.mem_map.mpr ⟨query, member, rfl⟩ :
      query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ∈
        Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.map
          (fun entry => entry.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)))

noncomputable def fixedLookup0 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.regIsZeroTable Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression0_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression0_1

noncomputable def fixedLookup1 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.u16SignTable Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression1_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression1_1

noncomputable def fixedLookup2 : Lookup Source.BaseField :=
  Verification.pairLookup Verification.conditionalTable Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression2_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression2_1

noncomputable def fixedLookup3 : Lookup Source.BaseField :=
  Verification.jumpCleanup Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression3_0 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression3_1 Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.genericExpression3_2

noncomputable def fixedLookups : List (Lookup Source.BaseField) := [fixedLookup0, fixedLookup1, fixedLookup2, fixedLookup3]

theorem generic_lookup0
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    fixedLookup0.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨0, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (1 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 9) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 9) = 1 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field0_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value0_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field0_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value0_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact NativePrimitiveMembership.JumpBranch.tag1_contains initial program setupRow selected _

theorem generic_lookup1
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    fixedLookup1.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨1, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (5 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 9) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 9) = 5 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field1_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value1_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field1_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value1_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact NativePrimitiveMembership.JumpBranch.tag5_contains initial program setupRow selected _

theorem generic_lookup2
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    fixedLookup2.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨2, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (31 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 9) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 9) = 31 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field2_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value2_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field2_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value2_1 physical data arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact NativePrimitiveMembership.JumpBranch.tag31_contains initial program setupRow selected _

theorem generic_lookup3
    (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    fixedLookup3.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨3, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (2 : Source.BaseField) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 9) at tagProof
  have selected : (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 9) = 2 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field3_0.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value3_0 physical data arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field3_1.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value3_1 physical data arithmetic).trans sourceCell1
  have sourceCell2 := congrArg (fun entries : List Source.BaseField => entries.getD 2 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field3_2.source.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = (NativePublicSetup.Proofs.genericCell initial program (.pooled .jumpBranchSlt) setupRow 2) at sourceCell2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value3_2 physical data arithmetic).trans sourceCell2
  apply clean_triple_lookup
  rw [same0, same1, same2]
  exact NativePrimitiveMembership.JumpBranch.tag2_contains initial program setupRow selected _

end Airbender.Compiler.NativeVectorLookups.JumpBranch
