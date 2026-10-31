import Airbender.Import.Compiler.LogicalRows.UnifiedCached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.UnifiedCached

namespace Airbender.Compiler.UnifiedRowNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The readable physical input contract has exactly the generated arithmetic
and execute-column interpretation; this equality changes no row condition. -/
theorem input_binding : Input = PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (fun _ _ => #[])).get
    Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1) := rfl

/-- The public address projection is exactly the retained generated Clean row
interpretation. This is a definitional binding, not an execution premise. -/
theorem inputRow_binding (input : Input) :
    inputRow input = (show Trace.Row babyBearModulus Trace.UnifiedFamily from
      ⟨.machine, (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment input.physical (fun _ _ => #[])).get⟩) := rfl

/-- Explicit public column-group selection agrees with the retained captured
lookup reduction's group ordering. -/
theorem lookupArguments_binding (input : Input) : LookupArguments input =
    ((group : Fin 3) → LookupArgument
      (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.setupColumns group))
      (activeLookupFields (nativeRequests input group))) := rfl

/-- Native base arithmetic transports the actual expanded operands to the
source-projected logical interface; none of the field equalities is a premise. -/
private theorem native_query25 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding25.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf25.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query25.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField25_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query26 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding26.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf26.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query26.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField26_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query27 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding27.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf27.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query27.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField27_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query28 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding28.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf28.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query28.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField28_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query29 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding29.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf29.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query29.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField29_9 input.physical copies) rfl)))))))))) rfl).symm

private theorem native_query20 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding20.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf20.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_9 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_10 input.physical copies) rfl)))))))))) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField20_0 input.physical copies)).symm

private theorem native_query0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf0.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField0_0 input.physical copies) rfl) rfl).symm

private theorem native_query2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf2.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField2_0 input.physical copies) rfl) rfl).symm

private theorem native_query3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf3.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField3_0 input.physical copies) rfl) rfl).symm

private theorem native_query4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf4.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query4.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField4_0 input.physical copies) rfl) rfl).symm

private theorem native_query5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf5.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query5.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField5_0 input.physical copies) rfl) rfl).symm

private theorem native_query6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf6.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query6.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField6_0 input.physical copies) rfl) rfl).symm

private theorem native_query7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf7.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query7.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField7_0 input.physical copies) rfl) rfl).symm

private theorem native_query8 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf8.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query8.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField8_0 input.physical copies) rfl) rfl).symm

private theorem native_query9 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf9.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query9.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField9_0 input.physical copies) rfl) rfl).symm

private theorem native_query10 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf10.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField10_0 input.physical copies) rfl) rfl).symm

private theorem native_query23 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding23.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf23.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query23.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField23_0 input.physical copies) rfl) rfl).symm

private theorem native_query11 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf11.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query11.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField11_0 input.physical copies) rfl) rfl).symm

private theorem native_query22 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding22.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf22.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query22.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.sourceField22_0 input.physical copies) rfl) rfl).symm

private theorem native_timestamp0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf12.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate12).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked12 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank12
    input.physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe12.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf14.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate14).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked14 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank14
    input.physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe14.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf15.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate15).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked15 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank15
    input.physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe15.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf16.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate16).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked16 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank16
    input.physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe16.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf17.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate17).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked17 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank17
    input.physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe17.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf18.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate18).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked18 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank18
    input.physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe18.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf19.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate19).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked19 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank19
    input.physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe19.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding24.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf24.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate24).sound
    Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
    Airbender.Compiler.HelperNative.UnifiedCached.native.checked24 Airbender.Compiler.HelperNative.UnifiedCached.native.inBank24
    input.physical (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.UnifiedCached.native.recipe24.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem nativeRequests_source (input : Input) (group : Fin 3) :
    nativeRequests input group = physicalRequests input group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding25.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf25.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding26.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf26.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding27.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf27.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding28.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf28.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding29.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf29.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding20.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf20.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query25.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query26.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query27.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query28.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query29.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query25 input) (congrArg₂ List.cons (native_query26 input) (congrArg₂ List.cons (native_query27 input) (congrArg₂ List.cons (native_query28 input) (congrArg₂ List.cons (native_query29 input) (congrArg₂ List.cons (native_query20 input) rfl))))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf0.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf2.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf3.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf4.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf5.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf6.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf7.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf8.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf9.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf10.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding23.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf23.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf11.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding22.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf22.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query4.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query5.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query6.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query7.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query8.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query9.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query23.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query11.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query22.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query0 input) (congrArg₂ List.cons (native_query2 input) (congrArg₂ List.cons (native_query3 input) (congrArg₂ List.cons (native_query4 input) (congrArg₂ List.cons (native_query5 input) (congrArg₂ List.cons (native_query6 input) (congrArg₂ List.cons (native_query7 input) (congrArg₂ List.cons (native_query8 input) (congrArg₂ List.cons (native_query9 input) (congrArg₂ List.cons (native_query10 input) (congrArg₂ List.cons (native_query23 input) (congrArg₂ List.cons (native_query11 input) (congrArg₂ List.cons (native_query22 input) rfl)))))))))))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf12.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf14.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf15.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf16.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf17.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf18.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf19.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding24.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf24.weight.value input.physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.UnifiedCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 input) (congrArg₂ List.cons (native_timestamp1 input) (congrArg₂ List.cons (native_timestamp2 input) (congrArg₂ List.cons (native_timestamp3 input) (congrArg₂ List.cons (native_timestamp4 input) (congrArg₂ List.cons (native_timestamp5 input) (congrArg₂ List.cons (native_timestamp6 input) (congrArg₂ List.cons (native_timestamp7 input) rfl))))))))

/-- Every native query leaf occurs once, with the single setup leaf completing
exactly the retained native reduction tree's primitive multiset. -/
theorem nativeOperands_coverage (input : Input) (group : Fin 3) :
    (((nativeOperands input group).map Prod.fst) ++ [nativeSetupLeaf group]).Perm
      (([Airbender.Compiler.LookupNative.UnifiedCached.native.genericTree,
      Airbender.Compiler.LookupNative.UnifiedCached.native.range16Tree,
      Airbender.Compiler.LookupNative.UnifiedCached.native.timestampTree]).get group).leaves := by
  fin_cases group

  · change ([25,
      26,
      27,
      28,
      29,
      20,
      21] : List Nat).Perm (Airbender.Compiler.LookupNative.UnifiedCached.native.genericTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([25,
      26,
      27,
      28,
      29,
      20,
      21] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericLeavesChecked) (by decide +kernel)

  · change ([0,
      2,
      3,
      4,
      5,
      6,
      7,
      8,
      9,
      10,
      23,
      11,
      22,
      1] : List Nat).Perm (Airbender.Compiler.LookupNative.UnifiedCached.native.range16Tree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([0,
      2,
      3,
      4,
      5,
      6,
      7,
      8,
      9,
      10,
      23,
      11,
      22,
      1] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16LeavesChecked) (by decide +kernel)

  · change ([12,
      14,
      15,
      16,
      17,
      18,
      19,
      24,
      13] : List Nat).Perm (Airbender.Compiler.LookupNative.UnifiedCached.native.timestampTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([12,
      14,
      15,
      16,
      17,
      18,
      19,
      24,
      13] : List Nat).Perm leaves)
      Airbender.Compiler.HelperNative.UnifiedCached.native.leavesChecked) (by decide +kernel)

/-- Each designated native setup operand contains precisely the columns used
by the literal setup table in the corresponding logical argument. -/
theorem nativeSetupColumns_binding (group : Fin 3) :
    ([Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding21.columns,
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding1.columns,
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding13.columns]).get group =
      (Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.setupColumns group).map
        (fun column => AffineProgram.input (Address := GKRAddress) (R := Nat) column.address) := by
  fin_cases group
  · exact Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.UnifiedCached.native.range16SetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.UnifiedCached.native.timestampSetupColumnsPreserved

/-- Exact native matching supplies every enabled source tuple in the supplied
setup rows. Native arithmetic proves the operand transport. -/
theorem source_member_with
    (tables : Fin 3 → Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length →
      List Source.BaseField) (input : Input) (arguments : LookupArgumentsWith tables input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    ∃ index, query.fields = tables group index := by
  apply LookupArgument.member (arguments group)
  change query.fields ∈ activeLookupFields (nativeRequests input group)
  rw [nativeRequests_source input group]
  exact activeLookupFields.member member enabled

private noncomputable def sourceArguments (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) : LookupArgument
      (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.setupColumns group))
      (activeLookupFields (physicalRequests input group)) := by
  simpa only [nativeRequests_source input group, Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.setupColumns] using arguments group
-- End native operand transport.

private theorem physical_member (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains
      (Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.setupColumns group) query.fields :=
  LookupArgument.member (sourceArguments input arguments group) (activeLookupFields.member member enabled)

/-- Authored lookup membership is proved at physical coordinates, without a
canonical source frame, using exact matching of the emitted tuples. -/
theorem authored_from_arguments (input : Input) (arguments : LookupArguments input) :
    PhysicalAuthoredLookupValid input.physical := by
  constructor
  · intro query member enabled
    apply physical_member input arguments 0 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)))
  · intro query member enabled
    apply physical_member input arguments 1 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)))

/-- The complete literal timestamp column, including zero padding, bounds
actual physical helper values. No canonical borrow choice is imposed. -/
theorem helpers_from_arguments (input : Input) (arguments : LookupArguments input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)
  have present := physical_member input arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.UnifiedCached.native.timestamp_bounded value present

theorem input_active (input : Input) :
    (inputRow input).assignment (inputRow input).columns.execute = 1 := input.active


end Airbender.Compiler.UnifiedRowNative.UnifiedCached
