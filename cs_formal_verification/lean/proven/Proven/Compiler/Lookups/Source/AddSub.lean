module
public import Proven.Compiler.Lookups.Tuples.AddSub
public import Proven.GKRProtocol.CleanArgumentsNative.AddSubCached
public import Proven.GKRProtocol.FunctionalLinksNative.AddSubCached
public import Proven.Compiler.Lookups.Membership
public import Proven.KernelExact
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Airbender.Compiler.NativeSourceTransport.AddSub
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def sourceRequests (physical : GKRAddress → Source.BaseField) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries.map (fun query => query.materialized
      ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.map (fun query => query.materialized
      ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.AddSubCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.AddSubCached.native.placement.project
        (physical ∘ Airbender.Compiler.MemoryNative.AddSubCached.native.bank.address))] 1)]).get group

noncomputable def legacyOperands (physical : GKRAddress → Source.BaseField) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf14.weight.value physical))],
      [(0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf0.weight.value physical)),
      (2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf2.weight.value physical)),
      (3, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf3.weight.value physical)),
      (4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf4.weight.value physical)),
      (5, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf5.weight.value physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf16.weight.value physical))],
      [(6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf6.weight.value physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf8.weight.value physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf9.weight.value physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf10.weight.value physical)),
      (11, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf11.weight.value physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf12.weight.value physical)),
      (13, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf13.weight.value physical)),
      (17, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf17.weight.value physical))]]).get group

noncomputable def legacyTuples (physical : GKRAddress → Source.BaseField) (group : Fin 3) :=
  (legacyOperands physical group).map Prod.snd

private theorem native_query14 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf14.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_8 physical copies) rfl)))))))) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField14_0 physical copies)).symm

private theorem native_query0 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf0.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query0.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField0_0 physical copies) rfl) rfl).symm

private theorem native_query2 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf2.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query2.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField2_0 physical copies) rfl) rfl).symm

private theorem native_query3 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf3.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query3.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField3_0 physical copies) rfl) rfl).symm

private theorem native_query4 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf4.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query4.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField4_0 physical copies) rfl) rfl).symm

private theorem native_query5 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf5.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query5.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField5_0 physical copies) rfl) rfl).symm

private theorem native_query16 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf16.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query16.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.AddSubCached.native.sourceField16_0 physical copies) rfl) rfl).symm

private theorem native_timestamp0 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf6.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate6).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked6 Airbender.Compiler.HelperNative.AddSubCached.native.inBank6
    physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe6.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf8.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate8).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked8 Airbender.Compiler.HelperNative.AddSubCached.native.inBank8
    physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe8.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf9.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate9).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked9 Airbender.Compiler.HelperNative.AddSubCached.native.inBank9
    physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe9.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf10.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate10).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked10 Airbender.Compiler.HelperNative.AddSubCached.native.inBank10
    physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe10.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf11.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate11).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked11 Airbender.Compiler.HelperNative.AddSubCached.native.inBank11
    physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe11.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf12.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate12).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked12 Airbender.Compiler.HelperNative.AddSubCached.native.inBank12
    physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe12.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf13.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate13).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked13 Airbender.Compiler.HelperNative.AddSubCached.native.inBank13
    physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe13.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf17.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.AddSubCached.native.candidate17).sound
    Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
    Airbender.Compiler.HelperNative.AddSubCached.native.checked17 Airbender.Compiler.HelperNative.AddSubCached.native.inBank17
    physical (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.AddSubCached.native.recipe17.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem legacyTuples_source (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) (group : Fin 3) :
    legacyTuples physical group = sourceRequests physical group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf14.weight.value physical)] =
      [Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query14 physical arithmetic) rfl)

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf0.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf2.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf3.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf4.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf5.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf16.weight.value physical)] =
      [Airbender.Compiler.LookupSourceNative.AddSubCached.native.query0.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query2.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query3.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query4.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query5.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.AddSubCached.native.query16.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query0 physical arithmetic) (congrArg₂ List.cons (native_query2 physical arithmetic) (congrArg₂ List.cons (native_query3 physical arithmetic) (congrArg₂ List.cons (native_query4 physical arithmetic) (congrArg₂ List.cons (native_query5 physical arithmetic) (congrArg₂ List.cons (native_query16 physical arithmetic) rfl))))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf6.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf8.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf9.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf10.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf11.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf12.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf13.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.fields physical)
        (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf17.weight.value physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.AddSubCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 physical arithmetic) (congrArg₂ List.cons (native_timestamp1 physical arithmetic) (congrArg₂ List.cons (native_timestamp2 physical arithmetic) (congrArg₂ List.cons (native_timestamp3 physical arithmetic) (congrArg₂ List.cons (native_timestamp4 physical arithmetic) (congrArg₂ List.cons (native_timestamp5 physical arithmetic) (congrArg₂ List.cons (native_timestamp6 physical arithmetic) (congrArg₂ List.cons (native_timestamp7 physical arithmetic) rfl))))))))


/-- The checked selector order and the source order contain the same native leaves. -/
theorem checkedTuples_permuted (physical : GKRAddress → Source.BaseField) (group : Fin 3) :
    (NativeLookups.TupleBindings.AddSub.checkedTuples physical group).Perm (legacyTuples physical group) := by
  obtain ⟨group, bound⟩ := group
  interval_cases group
  · kernel_exact (show ([0] : List Nat).Perm [0] from by decide).map
      (fun index => (legacyTuples physical ⟨0, by decide⟩).getD index ⟨[], 0⟩)
  · kernel_exact (show ([0, 1, 2, 3, 4, 5] : List Nat).Perm [0, 1, 2, 3, 4, 5] from by decide).map
      (fun index => (legacyTuples physical ⟨1, by decide⟩).getD index ⟨[], 0⟩)
  · kernel_exact (show ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).Perm [0, 1, 2, 3, 4, 5, 6, 7] from by decide).map
      (fun index => (legacyTuples physical ⟨2, by decide⟩).getD index ⟨[], 0⟩)

/-- Native base equations transport exact logical matching to source tuples. -/
noncomputable def matching {Index : Type} {physical : GKRAddress → Source.BaseField}
    {tables : Fin 3 → Index → List Source.BaseField}
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .addSub))
      (NativeLookups.selectorsFor (.pooled .addSub)) physical tables) :
    GroupedLookupArguments tables (fun group => activeLookupFields (sourceRequests physical group)) := by
  intro group
  let checked := NativeLookups.TupleBindings.AddSub.matching arguments group
  apply checked.reorder
  dsimp only
  rw [← legacyTuples_source physical arithmetic group]
  exact ((checkedTuples_permuted physical group).filter _).map _

/-- Each enabled physical source tuple equals an independently supplied setup row. -/
theorem source_member {Index : Type} {physical : GKRAddress → Source.BaseField}
    {tables : Fin 3 → Index → List Source.BaseField}
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .addSub))
      (NativeLookups.selectorsFor (.pooled .addSub)) physical tables)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ sourceRequests physical group) (enabled : query.weight ≠ 0) :
    ∃ index, query.fields = tables group index :=
  LookupArgument.member (matching arithmetic arguments group) (activeLookupFields.member member enabled)

end Airbender.Compiler.NativeSourceTransport.AddSub
