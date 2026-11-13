module
public import Proven.Compiler.Lookups.Tuples.SubwordMemory
public import Proven.GKRProtocol.CleanArgumentsNative.SubwordMemoryCached
public import Proven.GKRProtocol.FunctionalLinksNative.SubwordMemoryCached
public import Proven.Compiler.Lookups.Membership
public import Proven.KernelExact
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Airbender.Compiler.NativeSourceTransport.SubwordMemory
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def sourceRequests (physical : GKRAddress → Source.BaseField) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries.map (fun query => query.materialized
      ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.map (fun query => query.materialized
      ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement.project
        (physical ∘ Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address))] 1)]).get group

noncomputable def legacyOperands (physical : GKRAddress → Source.BaseField) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(17, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding17.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf17.weight.value physical)),
      (18, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding18.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf18.weight.value physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding12.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf12.weight.value physical))],
      [(14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding14.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf14.weight.value physical)),
      (0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding0.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf0.weight.value physical)),
      (15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding15.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf15.weight.value physical)),
      (2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding2.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf2.weight.value physical)),
      (3, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding3.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf3.weight.value physical))],
      [(4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding4.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf4.weight.value physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding6.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf6.weight.value physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding7.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf7.weight.value physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding8.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf8.weight.value physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding9.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf9.weight.value physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding10.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf10.weight.value physical)),
      (11, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding11.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf11.weight.value physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding16.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf16.weight.value physical))]]).get group

noncomputable def legacyTuples (physical : GKRAddress → Source.BaseField) (group : Fin 3) :=
  (legacyOperands physical group).map Prod.snd

private theorem native_query17 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding17.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf17.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query17.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_0 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField17_8 physical copies) rfl))))))))) rfl).symm

private theorem native_query18 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding18.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf18.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query18.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_0 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField18_8 physical copies) rfl))))))))) rfl).symm

private theorem native_query12 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding12.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf12.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_8 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_9 physical copies) rfl))))))))) (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField12_0 physical copies)).symm

private theorem native_query14 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding14.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf14.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query14.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField14_0 physical copies) rfl) rfl).symm

private theorem native_query0 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding0.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf0.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query0.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField0_0 physical copies) rfl) rfl).symm

private theorem native_query15 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding15.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf15.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query15.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField15_0 physical copies) rfl) rfl).symm

private theorem native_query2 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding2.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf2.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query2.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField2_0 physical copies) rfl) rfl).symm

private theorem native_query3 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding3.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf3.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query3.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.sourceField3_0 physical copies) rfl) rfl).symm

private theorem native_timestamp0 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding4.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf4.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate4).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked4 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank4
    physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe4.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding6.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf6.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate6).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked6 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank6
    physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe6.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding7.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf7.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate7).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked7 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank7
    physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe7.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding8.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf8.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate8).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked8 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank8
    physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe8.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding9.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf9.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate9).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked9 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank9
    physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe9.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding10.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf10.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate10).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked10 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank10
    physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe10.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding11.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf11.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate11).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked11 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank11
    physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe11.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding16.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf16.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.candidate16).sound
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.checked16 Airbender.Compiler.HelperNative.SubwordMemoryCached.native.inBank16
    physical (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.SubwordMemoryCached.native.recipe16.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem legacyTuples_source (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) (group : Fin 3) :
    legacyTuples physical group = sourceRequests physical group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding17.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf17.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding18.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf18.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding12.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf12.weight.value physical)] =
      [Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query17.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query18.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query17 physical arithmetic) (congrArg₂ List.cons (native_query18 physical arithmetic) (congrArg₂ List.cons (native_query12 physical arithmetic) rfl)))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding14.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf14.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding0.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf0.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding15.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf15.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding2.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf2.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding3.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf3.weight.value physical)] =
      [Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query14.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query0.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query15.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query2.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query3.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query14 physical arithmetic) (congrArg₂ List.cons (native_query0 physical arithmetic) (congrArg₂ List.cons (native_query15 physical arithmetic) (congrArg₂ List.cons (native_query2 physical arithmetic) (congrArg₂ List.cons (native_query3 physical arithmetic) rfl)))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding4.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf4.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding6.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf6.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding7.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf7.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding8.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf8.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding9.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf9.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding10.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf10.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding11.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf11.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding16.fields physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf16.weight.value physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 physical arithmetic) (congrArg₂ List.cons (native_timestamp1 physical arithmetic) (congrArg₂ List.cons (native_timestamp2 physical arithmetic) (congrArg₂ List.cons (native_timestamp3 physical arithmetic) (congrArg₂ List.cons (native_timestamp4 physical arithmetic) (congrArg₂ List.cons (native_timestamp5 physical arithmetic) (congrArg₂ List.cons (native_timestamp6 physical arithmetic) (congrArg₂ List.cons (native_timestamp7 physical arithmetic) rfl))))))))


/-- The checked selector order and the source order contain the same native leaves. -/
theorem checkedTuples_permuted (physical : GKRAddress → Source.BaseField) (group : Fin 3) :
    (NativeLookups.TupleBindings.SubwordMemory.checkedTuples physical group).Perm (legacyTuples physical group) := by
  obtain ⟨group, bound⟩ := group
  interval_cases group
  · kernel_exact (show ([2, 0, 1] : List Nat).Perm [0, 1, 2] from by decide).map
      (fun index => (legacyTuples physical ⟨0, by decide⟩).getD index ⟨[], 0⟩)
  · kernel_exact (show ([1, 3, 4, 0, 2] : List Nat).Perm [0, 1, 2, 3, 4] from by decide).map
      (fun index => (legacyTuples physical ⟨1, by decide⟩).getD index ⟨[], 0⟩)
  · kernel_exact (show ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).Perm [0, 1, 2, 3, 4, 5, 6, 7] from by decide).map
      (fun index => (legacyTuples physical ⟨2, by decide⟩).getD index ⟨[], 0⟩)

/-- Native base equations transport exact logical matching to source tuples. -/
noncomputable def matching {Index : Type} {physical : GKRAddress → Source.BaseField}
    {tables : Fin 3 → Index → List Source.BaseField}
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical tables) :
    GroupedLookupArguments tables (fun group => activeLookupFields (sourceRequests physical group)) := by
  intro group
  let checked := NativeLookups.TupleBindings.SubwordMemory.matching arguments group
  apply checked.reorder
  dsimp only
  rw [← legacyTuples_source physical arithmetic group]
  exact ((checkedTuples_permuted physical group).filter _).map _

/-- Each enabled physical source tuple equals an independently supplied setup row. -/
theorem source_member {Index : Type} {physical : GKRAddress → Source.BaseField}
    {tables : Fin 3 → Index → List Source.BaseField}
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical tables)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ sourceRequests physical group) (enabled : query.weight ≠ 0) :
    ∃ index, query.fields = tables group index :=
  LookupArgument.member (matching arithmetic arguments group) (activeLookupFields.member member enabled)

end Airbender.Compiler.NativeSourceTransport.SubwordMemory
