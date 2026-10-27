import Airbender.Import.Compiler.LogicalRows.MulDivCached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.MulDivCached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.MulDivCached
import Airbender.Proofs.GKRProtocol.PooledRowNative.MulDivCached

namespace Airbender.Compiler.PooledRowNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The readable physical input contract has exactly the generated arithmetic
and execute-column interpretation; this equality changes no row condition. -/
theorem input_binding : Input = PhysicalRowInput
    (fun physical => ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates,
    gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (fun physical => (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical (fun _ _ => #[])).get
    Airbender.MulDiv.importedConstraintsTraceColumns.execute = 1) := rfl

/-- The public address projection is exactly the retained generated Clean row
interpretation. This is a definitional binding, not an execution premise. -/
theorem inputRow_binding (input : Input) :
    inputRow input = (show Trace.Row babyBearModulus Trace.PooledFamily from
      ⟨.mulDiv, (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment input.physical (fun _ _ => #[])).get⟩) := rfl

/-- Explicit public column-group selection agrees with the retained captured
lookup reduction's group ordering. -/
theorem lookupArguments_binding (input : Input) : LookupArguments input =
    ((group : Fin 3) → LookupArgument
      (Airbender.Compiler.MaterializedNative.MulDivCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.MulDivCached.setupColumns group))
      (activeLookupFields (nativeRequests input group))) := rfl

/-- Native base arithmetic transports the actual expanded operands to the
source-projected logical interface; none of the field equalities is a premise. -/
private theorem native_query18 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf18.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField18_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField18_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField18_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField18_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField18_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField18_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField18_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField18_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField18_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query19 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf19.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query19.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField19_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField19_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField19_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField19_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField19_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField19_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField19_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField19_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField19_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query20 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding20.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf20.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query20.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField20_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField20_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField20_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField20_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField20_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField20_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField20_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField20_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField20_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query21 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding21.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf21.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query21.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField21_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField21_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField21_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField21_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField21_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField21_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField21_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField21_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField21_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query22 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding22.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf22.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query22.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField22_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField22_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField22_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField22_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField22_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField22_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField22_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField22_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField22_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query23 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding23.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf23.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query23.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField23_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField23_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField23_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField23_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField23_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField23_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField23_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField23_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField23_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query26 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding26.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf26.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query26.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField26_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField26_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField26_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField26_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField26_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField26_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField26_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField26_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField26_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query27 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding27.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf27.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query27.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField27_0 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField27_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField27_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField27_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField27_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField27_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField27_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField27_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField27_8 input.physical copies) rfl))))))))) rfl).symm

private theorem native_query16 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf16.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_1 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_2 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_3 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_4 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_5 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_6 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_7 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_8 input.physical copies) (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_9 input.physical copies) rfl))))))))) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField16_0 input.physical copies)).symm

private theorem native_query0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf0.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField0_0 input.physical copies) rfl) rfl).symm

private theorem native_query2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf2.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField2_0 input.physical copies) rfl) rfl).symm

private theorem native_query3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf3.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField3_0 input.physical copies) rfl) rfl).symm

private theorem native_query4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf4.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query4.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField4_0 input.physical copies) rfl) rfl).symm

private theorem native_query5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf5.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query5.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField5_0 input.physical copies) rfl) rfl).symm

private theorem native_query6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf6.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query6.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField6_0 input.physical copies) rfl) rfl).symm

private theorem native_query7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf7.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query7.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField7_0 input.physical copies) rfl) rfl).symm

private theorem native_query24 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding24.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf24.weight.value input.physical) =
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query24.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) :=
  let copies := Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.lookupCopies input.physical input.arithmetic
  (congrArg₂ MaterializedQuery.mk (congrArg₂ List.cons (Airbender.Compiler.LookupSourceNative.MulDivCached.native.sourceField24_0 input.physical copies) rfl) rfl).symm

private theorem native_timestamp0 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf8.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.MulDivCached.native.candidate8).sound
    Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
    Airbender.Compiler.HelperNative.MulDivCached.native.checked8 Airbender.Compiler.HelperNative.MulDivCached.native.inBank8
    input.physical (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampFieldMatch0] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.MulDivCached.native.recipe8.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp1 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf10.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.MulDivCached.native.candidate10).sound
    Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
    Airbender.Compiler.HelperNative.MulDivCached.native.checked10 Airbender.Compiler.HelperNative.MulDivCached.native.inBank10
    input.physical (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampFieldMatch1] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.MulDivCached.native.recipe10.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp2 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf11.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.MulDivCached.native.candidate11).sound
    Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
    Airbender.Compiler.HelperNative.MulDivCached.native.checked11 Airbender.Compiler.HelperNative.MulDivCached.native.inBank11
    input.physical (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampFieldMatch2] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.MulDivCached.native.recipe11.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp3 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf12.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.MulDivCached.native.candidate12).sound
    Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
    Airbender.Compiler.HelperNative.MulDivCached.native.checked12 Airbender.Compiler.HelperNative.MulDivCached.native.inBank12
    input.physical (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampFieldMatch3] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.MulDivCached.native.recipe12.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp4 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf13.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.MulDivCached.native.candidate13).sound
    Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
    Airbender.Compiler.HelperNative.MulDivCached.native.checked13 Airbender.Compiler.HelperNative.MulDivCached.native.inBank13
    input.physical (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampFieldMatch4] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.MulDivCached.native.recipe13.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp5 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf14.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.MulDivCached.native.candidate14).sound
    Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
    Airbender.Compiler.HelperNative.MulDivCached.native.checked14 Airbender.Compiler.HelperNative.MulDivCached.native.inBank14
    input.physical (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampFieldMatch5] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.MulDivCached.native.recipe14.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp6 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf15.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.MulDivCached.native.candidate15).sound
    Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
    Airbender.Compiler.HelperNative.MulDivCached.native.checked15 Airbender.Compiler.HelperNative.MulDivCached.native.inBank15
    input.physical (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampFieldMatch6] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.MulDivCached.native.recipe15.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

private theorem native_timestamp7 (input : Input) :
    MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding25.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf25.weight.value input.physical) =
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1 := by
  have same := (Airbender.Compiler.HelperNative.MulDivCached.native.candidate25).sound
    Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
    Airbender.Compiler.HelperNative.MulDivCached.native.checked25 Airbender.Compiler.HelperNative.MulDivCached.native.inBank25
    input.physical (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.helperCopies input.physical input.arithmetic)
  rw [Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampFieldMatch7] at same
  change MaterializedQuery.mk [Airbender.Compiler.HelperNative.MulDivCached.native.recipe25.value input.physical] 1 = _
  exact congrArg (fun value : Source.BaseField => MaterializedQuery.mk [value] 1) same.symm

/-- Native base arithmetic identifies each enabled expanded payload and mask
with its source interpretation, including every timestamp helper. -/
theorem nativeRequests_source (input : Input) (group : Fin 3) :
    nativeRequests input group = physicalRequests input group := by
  fin_cases group

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf18.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf19.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding20.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf20.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding21.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf21.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding22.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf22.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding23.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf23.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding26.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf26.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding27.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf27.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf16.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.MulDivCached.native.query18.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query19.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query20.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query21.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query22.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query23.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query26.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query27.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query18 input) (congrArg₂ List.cons (native_query19 input) (congrArg₂ List.cons (native_query20 input) (congrArg₂ List.cons (native_query21 input) (congrArg₂ List.cons (native_query22 input) (congrArg₂ List.cons (native_query23 input) (congrArg₂ List.cons (native_query26 input) (congrArg₂ List.cons (native_query27 input) (congrArg₂ List.cons (native_query16 input) rfl)))))))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf0.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf2.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf3.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf4.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf5.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf6.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf7.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding24.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf24.weight.value input.physical)] =
      [Airbender.Compiler.LookupSourceNative.MulDivCached.native.query0.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query2.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query3.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query4.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query5.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query6.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query7.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement),
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.query24.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)]
    exact (congrArg₂ List.cons (native_query0 input) (congrArg₂ List.cons (native_query2 input) (congrArg₂ List.cons (native_query3 input) (congrArg₂ List.cons (native_query4 input) (congrArg₂ List.cons (native_query5 input) (congrArg₂ List.cons (native_query6 input) (congrArg₂ List.cons (native_query7 input) (congrArg₂ List.cons (native_query24 input) rfl))))))))

  · change [MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf8.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf10.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf11.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf12.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf13.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf14.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf15.weight.value input.physical),
      MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding25.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf25.weight.value input.physical)] =
      [MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨0, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨1, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨2, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨3, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨4, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨5, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨6, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1,
      MaterializedQuery.mk [((Airbender.Compiler.HelperNative.MulDivCached.native.fields).get ⟨7, by decide⟩).value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1]
    exact (congrArg₂ List.cons (native_timestamp0 input) (congrArg₂ List.cons (native_timestamp1 input) (congrArg₂ List.cons (native_timestamp2 input) (congrArg₂ List.cons (native_timestamp3 input) (congrArg₂ List.cons (native_timestamp4 input) (congrArg₂ List.cons (native_timestamp5 input) (congrArg₂ List.cons (native_timestamp6 input) (congrArg₂ List.cons (native_timestamp7 input) rfl))))))))

/-- Every native query leaf occurs once, with the single setup leaf completing
exactly the retained native reduction tree's primitive multiset. -/
theorem nativeOperands_coverage (input : Input) (group : Fin 3) :
    (((nativeOperands input group).map Prod.fst) ++ [nativeSetupLeaf group]).Perm
      (([Airbender.Compiler.LookupNative.MulDivCached.native.genericTree,
      Airbender.Compiler.LookupNative.MulDivCached.native.range16Tree,
      Airbender.Compiler.LookupNative.MulDivCached.native.timestampTree]).get group).leaves := by
  fin_cases group

  · change ([18,
      19,
      20,
      21,
      22,
      23,
      26,
      27,
      16,
      17] : List Nat).Perm (Airbender.Compiler.LookupNative.MulDivCached.native.genericTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([18,
      19,
      20,
      21,
      22,
      23,
      26,
      27,
      16,
      17] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericLeavesChecked) (by decide +kernel)

  · change ([0,
      2,
      3,
      4,
      5,
      6,
      7,
      24,
      1] : List Nat).Perm (Airbender.Compiler.LookupNative.MulDivCached.native.range16Tree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([0,
      2,
      3,
      4,
      5,
      6,
      7,
      24,
      1] : List Nat).Perm leaves)
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16LeavesChecked) (by decide +kernel)

  · change ([8,
      10,
      11,
      12,
      13,
      14,
      15,
      25,
      9] : List Nat).Perm (Airbender.Compiler.LookupNative.MulDivCached.native.timestampTree).leaves
    exact Eq.mpr (congrArg (fun leaves : List Nat => ([8,
      10,
      11,
      12,
      13,
      14,
      15,
      25,
      9] : List Nat).Perm leaves)
      Airbender.Compiler.HelperNative.MulDivCached.native.leavesChecked) (by decide +kernel)

/-- Each designated native setup operand contains precisely the columns used
by the literal setup table in the corresponding logical argument. -/
theorem nativeSetupColumns_binding (group : Fin 3) :
    ([Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding17.columns,
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding1.columns,
      Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding9.columns]).get group =
      (Airbender.Compiler.MaterializedWitnessNative.MulDivCached.setupColumns group).map
        (fun column => AffineProgram.input (Address := GKRAddress) (R := Nat) column.address) := by
  fin_cases group
  · exact Airbender.Compiler.TableNative.MulDivCached.native.genericSetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.MulDivCached.native.range16SetupColumnsPreserved
  · exact Airbender.Compiler.TableNative.MulDivCached.native.timestampSetupColumnsPreserved

private noncomputable def sourceArguments (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) : LookupArgument
      (Airbender.Compiler.MaterializedNative.MulDivCached.native.model.fields
        (Airbender.Compiler.MaterializedWitnessNative.MulDivCached.setupColumns group))
      (activeLookupFields (physicalRequests input group)) := by
  simpa only [nativeRequests_source input group, Airbender.Compiler.MaterializedWitnessNative.MulDivCached.setupColumns] using arguments group
-- End native operand transport.

private theorem physical_member (input : Input) (arguments : LookupArguments input)
    (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains
      (Airbender.Compiler.MaterializedWitnessNative.MulDivCached.setupColumns group) query.fields :=
  LookupArgument.member (sourceArguments input arguments group) (activeLookupFields.member member enabled)

/-- Authored lookup membership is proved at physical coordinates, without a
canonical source frame, using exact matching of the emitted tuples. -/
theorem authored_from_arguments (input : Input) (arguments : LookupArguments input) :
    PhysicalAuthoredLookupValid input.physical := by
  constructor
  · intro query member enabled
    apply physical_member input arguments 0 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)))
  · intro query member enabled
    apply physical_member input arguments 1 (query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)) ?_ enabled
    simpa [physicalRequests] using
      (List.mem_map.mpr ⟨query, member, rfl⟩ :
        query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ∈
          Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.map (fun item => item.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)))

/-- The complete literal timestamp column, including zero padding, bounds
actual physical helper values. No canonical borrow choice is imposed. -/
theorem helpers_from_arguments (input : Input) (arguments : LookupArguments input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.MulDivCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)
  have present := physical_member input arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.MulDivCached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.MulDivCached.native.timestamp_bounded value present

theorem input_active (input : Input) :
    (inputRow input).assignment (inputRow input).columns.execute = 1 := input.active

theorem input_constraints (input : Input) (arguments : LookupArguments input) {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (physical : Trace.initialImage before cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨Trace.ROM.table cells tokens,
        Verification.subwordTable (Trace.ROM.words before)⟩ : Trace.PooledSetup babyBearModulus)) := by
  have native := Airbender.Compiler.PhysicalClosedNative.MulDivCached.retained_clock_from_physical
    input.physical (fun _ _ => #[]) input.arithmetic (helpers_from_arguments input arguments)
    (authored_from_arguments input arguments)
  exact native

/-- Decode by transporting physical table membership directly through the
checked decoder-payload geometry. No canonical borrow frame is needed. -/
theorem input_decoded (input : Input) (arguments : LookupArguments input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.pooledProgram (inputRow input).family).Contains #[]
      (inputRow input).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.MulDivCached.program_from_source_membership (by decide +kernel)
    input.physical (fun _ _ => #[]) input.arithmetic typed
  apply (authored_from_arguments input arguments).1 Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16
    Airbender.Compiler.DecoderQueryNative.MulDivCached.decoder_query_member
  rw [Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have enabled : (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.MulDiv.importedConstraintsTraceColumns.execute = 1 := input.active
  have nonzero : (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.MulDiv.importedConstraintsTraceColumns.execute ≠ 0 :=
    fun zero => one_ne_zero (enabled.symm.trans zero)
  simpa [Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression0, _root_.Expression.eval] using nonzero

end Airbender.Compiler.PooledRowNative.MulDivCached
