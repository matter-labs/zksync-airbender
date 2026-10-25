import GKRProtocol.CleanClosedParts.KeccakUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup0
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨0, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field0_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨0, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field0_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value0_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field0_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨1, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field0_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value0_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field0_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨2, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field0_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value0_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field0_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨3, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field0_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value0_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field0_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨4, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field0_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value0_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field0_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨5, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field0_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value0_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field0_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨6, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field0_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value0_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field0_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨7, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field0_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value0_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup1
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions1).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨1, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field1_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨8, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field1_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value1_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field1_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨9, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field1_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value1_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field1_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨10, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field1_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value1_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field1_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨11, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field1_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value1_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field1_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨12, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field1_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value1_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field1_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨13, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field1_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value1_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field1_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨14, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field1_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value1_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field1_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨15, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field1_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value1_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup2
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions2).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨2, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field2_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨16, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field2_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value2_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field2_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨17, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field2_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value2_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field2_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨18, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field2_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value2_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field2_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨19, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field2_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value2_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field2_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨20, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field2_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value2_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field2_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨21, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field2_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value2_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field2_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨22, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field2_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value2_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field2_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨23, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field2_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value2_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions2, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup3
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions3).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨3, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field3_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨24, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field3_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value3_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field3_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨25, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field3_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value3_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field3_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨26, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field3_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value3_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field3_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨27, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field3_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value3_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field3_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨28, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field3_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value3_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field3_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨29, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field3_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value3_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field3_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨30, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field3_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value3_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field3_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨31, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field3_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value3_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions3, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup4
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions4).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨4, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field4_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨32, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field4_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value4_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field4_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨33, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field4_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value4_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field4_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨34, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field4_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value4_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field4_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨35, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field4_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value4_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field4_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨36, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field4_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value4_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field4_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨37, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field4_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value4_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field4_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨38, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field4_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value4_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field4_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨39, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field4_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value4_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions4, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup5
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions5).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨5, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field5_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨40, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field5_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value5_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field5_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨41, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field5_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value5_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field5_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨42, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field5_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value5_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field5_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨43, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field5_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value5_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field5_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨44, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field5_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value5_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field5_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨45, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field5_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value5_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field5_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨46, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field5_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value5_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field5_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨47, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field5_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value5_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions5, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup6
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions6).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨6, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field6_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨48, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field6_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value6_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field6_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨49, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field6_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value6_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field6_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨50, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field6_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value6_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field6_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨51, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field6_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value6_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field6_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨52, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field6_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value6_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field6_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨53, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field6_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value6_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field6_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨54, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field6_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value6_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field6_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨55, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field6_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value6_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions6, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup7
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions7).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨7, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field7_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨56, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field7_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value7_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field7_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨57, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field7_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value7_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field7_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨58, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field7_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value7_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field7_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨59, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field7_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value7_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field7_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨60, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field7_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value7_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field7_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨61, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field7_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value7_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field7_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨62, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field7_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value7_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field7_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨63, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field7_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.generic_value7_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions7, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid


end Airbender.Compiler.CleanClosedNative.KeccakUncached
