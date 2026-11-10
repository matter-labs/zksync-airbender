import Airbender.Proofs.GKRProtocol.CleanClosedParts.BlakeRoundCached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup48
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions48).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨48, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨48, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨288, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value48_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨289, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value48_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨290, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value48_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨291, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value48_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨292, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value48_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨293, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field48_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value48_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions48, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression48_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression48_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression48_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression48_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression48_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression48_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup49
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions49).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨49, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨49, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨294, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value49_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨295, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value49_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨296, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value49_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨297, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value49_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨298, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value49_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨299, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field49_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value49_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions49, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression49_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression49_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression49_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression49_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression49_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression49_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup50
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions50).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨50, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨50, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨300, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value50_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨301, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value50_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨302, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value50_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨303, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value50_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨304, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value50_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨305, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field50_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value50_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions50, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression50_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression50_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression50_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression50_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression50_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression50_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup51
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions51).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨51, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨51, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨306, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value51_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨307, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value51_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨308, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value51_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨309, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value51_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨310, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value51_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨311, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field51_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value51_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions51, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression51_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression51_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression51_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression51_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression51_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression51_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup52
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions52).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨52, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨52, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨312, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value52_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨313, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value52_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨314, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value52_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨315, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value52_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨316, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value52_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨317, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field52_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value52_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions52, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression52_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression52_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression52_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression52_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression52_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression52_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup53
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions53).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨53, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨53, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨318, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value53_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨319, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value53_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨320, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value53_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨321, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value53_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨322, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value53_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨323, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field53_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value53_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions53, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression53_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression53_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression53_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression53_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression53_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression53_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup54
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions54).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨54, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨54, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨324, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value54_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨325, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value54_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨326, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value54_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨327, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value54_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨328, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value54_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨329, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field54_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value54_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions54, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression54_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression54_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression54_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression54_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression54_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression54_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup55
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions55).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries.get ⟨55, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries ⟨55, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨330, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value55_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨331, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value55_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨332, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value55_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨333, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value55_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨334, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value55_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields ⟨335, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundCached.native.field55_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.generic_value55_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions55, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression55_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression55_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression55_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression55_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression55_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.part6.genericExpression55_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeRoundCached
