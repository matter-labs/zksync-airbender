module
public import Proven.Compiler.Lookups.Tuples.Unified
public import Proven.GKRProtocol.CleanArgumentsNative.UnifiedCached
public import Proven.GKRProtocol.FunctionalLinksNative.UnifiedCached
public import Proven.Compiler.Lookups.Membership
public import Proven.KernelExact
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Airbender.Compiler.NativeSourceTransport.Unified
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def sourceRequests (physical : GKRAddress → Source.BaseField) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.map (fun query => query.materialized
      ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.map (fun query => query.materialized
      ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.placement.project
        (physical ∘ Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.address))] 1)]).get group

noncomputable def legacyOperands (physical : GKRAddress → Source.BaseField) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(25, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding25.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf25.weight.value physical)),
      (26, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding26.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf26.weight.value physical)),
      (27, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding27.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf27.weight.value physical)),
      (28, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding28.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf28.weight.value physical)),
      (29, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding29.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf29.weight.value physical)),
      (20, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding20.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf20.weight.value physical))],
      [(0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding0.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf0.weight.value physical)),
      (2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding2.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf2.weight.value physical)),
      (3, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding3.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf3.weight.value physical)),
      (4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding4.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf4.weight.value physical)),
      (5, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding5.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf5.weight.value physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding6.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf6.weight.value physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding7.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf7.weight.value physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding8.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf8.weight.value physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding9.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf9.weight.value physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding10.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf10.weight.value physical)),
      (23, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding23.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf23.weight.value physical)),
      (11, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding11.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf11.weight.value physical)),
      (22, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding22.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf22.weight.value physical))],
      [(12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding12.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf12.weight.value physical)),
      (14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding14.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf14.weight.value physical)),
      (15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding15.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf15.weight.value physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding16.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf16.weight.value physical)),
      (17, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding17.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf17.weight.value physical)),
      (18, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding18.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf18.weight.value physical)),
      (19, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding19.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf19.weight.value physical)),
      (24, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding24.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf24.weight.value physical))]]).get group

noncomputable def legacyTuples (physical : GKRAddress → Source.BaseField) (group : Fin 3) :=
  (legacyOperands physical group).map Prod.snd

private theorem native_query25 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding25.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf25.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query25.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_0 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_8 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_9 physical copies) rfl)))))))))) rfl).symm

private theorem native_query26 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding26.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf26.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query26.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_0 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_8 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_9 physical copies) rfl)))))))))) rfl).symm

private theorem native_query27 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding27.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf27.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query27.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_0 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_8 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_9 physical copies) rfl)))))))))) rfl).symm

private theorem native_query28 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding28.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf28.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query28.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_0 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_8 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_9 physical copies) rfl)))))))))) rfl).symm

private theorem native_query29 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding29.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf29.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query29.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_0 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_8 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_9 physical copies) rfl)))))))))) rfl).symm

private theorem native_query20 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding20.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf20.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_1 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_2 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_3 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_4 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_5 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_6 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_7 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_8 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_9 physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_10 physical copies) rfl)))))))))) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_0 physical copies)).symm

private theorem native_query0 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding0.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf0.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query0.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField0_0 physical copies) rfl) rfl).symm

private theorem native_query2 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding2.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf2.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query2.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField2_0 physical copies) rfl) rfl).symm

private theorem native_query3 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding3.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf3.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query3.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField3_0 physical copies) rfl) rfl).symm

private theorem native_query4 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding4.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf4.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query4.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField4_0 physical copies) rfl) rfl).symm

private theorem native_query5 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding5.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf5.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query5.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField5_0 physical copies) rfl) rfl).symm

private theorem native_query6 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding6.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf6.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query6.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField6_0 physical copies) rfl) rfl).symm

private theorem native_query7 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding7.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf7.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query7.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField7_0 physical copies) rfl) rfl).symm

private theorem native_query8 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding8.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf8.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query8.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField8_0 physical copies) rfl) rfl).symm

private theorem native_query9 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding9.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf9.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query9.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField9_0 physical copies) rfl) rfl).symm

private theorem native_query10 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding10.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf10.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query10.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField10_0 physical copies) rfl) rfl).symm

private theorem native_query23 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding23.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf23.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query23.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField23_0 physical copies) rfl) rfl).symm

private theorem native_query11 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding11.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf11.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query11.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField11_0 physical copies) rfl) rfl).symm

private theorem native_query22 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding22.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf22.weight.value physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query22.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies physical arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField22_0 physical copies) rfl) rfl).symm

private theorem native_timestamp0 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding12.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf12.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate12).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked12 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank12
    physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe12.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding14.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf14.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate14).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked14 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank14
    physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe14.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding15.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf15.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate15).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked15 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank15
    physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe15.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding16.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf16.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate16).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked16 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank16
    physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe16.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding17.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf17.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate17).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked17 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank17
    physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe17.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding18.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf18.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate18).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked18 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank18
    physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe18.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding19.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf19.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate19).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked19 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank19
    physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe19.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding24.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf24.weight.value physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate24).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked24 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank24
    physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies physical arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe24.value physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem legacyTuples_source (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) (group : Fin 3) :
    legacyTuples physical group = sourceRequests physical group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding25.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf25.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding26.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf26.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding27.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf27.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding28.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf28.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding29.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf29.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding20.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf20.weight.value physical)] =
      [Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query25.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query26.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query27.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query28.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query29.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query25 physical arithmetic) (congrArg₂ List.cons (native_query26 physical arithmetic) (congrArg₂ List.cons (native_query27 physical arithmetic) (congrArg₂ List.cons (native_query28 physical arithmetic) (congrArg₂ List.cons (native_query29 physical arithmetic) (congrArg₂ List.cons (native_query20 physical arithmetic) rfl))))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding0.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf0.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding2.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf2.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding3.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf3.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding4.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf4.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding5.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf5.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding6.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf6.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding7.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf7.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding8.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf8.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding9.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf9.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding10.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf10.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding23.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf23.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding11.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf11.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding22.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf22.weight.value physical)] =
      [Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query0.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query2.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query3.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query4.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query5.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query6.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query7.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query8.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query9.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query10.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query23.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query11.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query22.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query0 physical arithmetic) (congrArg₂ List.cons (native_query2 physical arithmetic) (congrArg₂ List.cons (native_query3 physical arithmetic) (congrArg₂ List.cons (native_query4 physical arithmetic) (congrArg₂ List.cons (native_query5 physical arithmetic) (congrArg₂ List.cons (native_query6 physical arithmetic) (congrArg₂ List.cons (native_query7 physical arithmetic) (congrArg₂ List.cons (native_query8 physical arithmetic) (congrArg₂ List.cons (native_query9 physical arithmetic) (congrArg₂ List.cons (native_query10 physical arithmetic) (congrArg₂ List.cons (native_query23 physical arithmetic) (congrArg₂ List.cons (native_query11 physical arithmetic) (congrArg₂ List.cons (native_query22 physical arithmetic) rfl)))))))))))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding12.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf12.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding14.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf14.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding15.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf15.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding16.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf16.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding17.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf17.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding18.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf18.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding19.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf19.weight.value physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding24.fields physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf24.weight.value physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 physical arithmetic) (congrArg₂ List.cons (native_timestamp1 physical arithmetic) (congrArg₂ List.cons (native_timestamp2 physical arithmetic) (congrArg₂ List.cons (native_timestamp3 physical arithmetic) (congrArg₂ List.cons (native_timestamp4 physical arithmetic) (congrArg₂ List.cons (native_timestamp5 physical arithmetic) (congrArg₂ List.cons (native_timestamp6 physical arithmetic) (congrArg₂ List.cons (native_timestamp7 physical arithmetic) rfl))))))))


/-- The checked selector order and the source order contain the same native leaves. -/
theorem checkedTuples_permuted (physical : GKRAddress → Source.BaseField) (group : Fin 3) :
    (NativeLookups.TupleBindings.Unified.checkedTuples physical group).Perm (legacyTuples physical group) := by
  obtain ⟨group, bound⟩ := group
  interval_cases group
  · kernel_exact (show ([5, 0, 1, 2, 3, 4] : List Nat).Perm [0, 1, 2, 3, 4, 5] from by decide).map
      (fun index => (legacyTuples physical ⟨0, by decide⟩).getD index ⟨[], 0⟩)
  · kernel_exact (show ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 10] : List Nat).Perm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by decide).map
      (fun index => (legacyTuples physical ⟨1, by decide⟩).getD index ⟨[], 0⟩)
  · kernel_exact (show ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).Perm [0, 1, 2, 3, 4, 5, 6, 7] from by decide).map
      (fun index => (legacyTuples physical ⟨2, by decide⟩).getD index ⟨[], 0⟩)

/-- Native base equations transport exact logical matching to source tuples. -/
noncomputable def matching {Index : Type} {physical : GKRAddress → Source.BaseField}
    {tables : Fin 3 → Index → List Source.BaseField}
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical tables) :
    GroupedLookupArguments tables (fun group => activeLookupFields (sourceRequests physical group)) := by
  intro group
  let checked := NativeLookups.TupleBindings.Unified.matching arguments group
  apply checked.reorder
  dsimp only
  rw [← legacyTuples_source physical arithmetic group]
  exact ((checkedTuples_permuted physical group).filter _).map _

/-- Each enabled physical source tuple equals an independently supplied setup row. -/
theorem source_member {Index : Type} {physical : GKRAddress → Source.BaseField}
    {tables : Fin 3 → Index → List Source.BaseField}
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical tables)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ sourceRequests physical group) (enabled : query.weight ≠ 0) :
    ∃ index, query.fields = tables group index :=
  LookupArgument.member (matching arithmetic arguments group) (activeLookupFields.member member enabled)

end Airbender.Compiler.NativeSourceTransport.Unified
