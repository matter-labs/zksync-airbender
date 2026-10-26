import Airbender.Proofs.GKRProtocol.CleanClosedParts.KeccakUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup32
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions32).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨32, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨32, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field32_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨256, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field32_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value32_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field32_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨257, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field32_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value32_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field32_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨258, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field32_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value32_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field32_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨259, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field32_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value32_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field32_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨260, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field32_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value32_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field32_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨261, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field32_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value32_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field32_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨262, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field32_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value32_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field32_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨263, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field32_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value32_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions32, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup33
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions33).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨33, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨33, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field33_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨264, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field33_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value33_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field33_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨265, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field33_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value33_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field33_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨266, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field33_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value33_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field33_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨267, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field33_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value33_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field33_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨268, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field33_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value33_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field33_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨269, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field33_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value33_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field33_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨270, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field33_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value33_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field33_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨271, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field33_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value33_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions33, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup34
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions34).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨34, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨34, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field34_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨272, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field34_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value34_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field34_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨273, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field34_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value34_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field34_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨274, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field34_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value34_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field34_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨275, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field34_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value34_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field34_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨276, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field34_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value34_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field34_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨277, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field34_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value34_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field34_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨278, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field34_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value34_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field34_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨279, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field34_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value34_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions34, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup35
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions35).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨35, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨35, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field35_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨280, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field35_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value35_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field35_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨281, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field35_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value35_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field35_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨282, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field35_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value35_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field35_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨283, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field35_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value35_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field35_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨284, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field35_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value35_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field35_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨285, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field35_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value35_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field35_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨286, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field35_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value35_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field35_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨287, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field35_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value35_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions35, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup36
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions36).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨36, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨36, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field36_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨288, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field36_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value36_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field36_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨289, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field36_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value36_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field36_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨290, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field36_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value36_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field36_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨291, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field36_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value36_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field36_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨292, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field36_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value36_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field36_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨293, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field36_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value36_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field36_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨294, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field36_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value36_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field36_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨295, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field36_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value36_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions36, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup37
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions37).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨37, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨37, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field37_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨296, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field37_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value37_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field37_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨297, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field37_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value37_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field37_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨298, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field37_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value37_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field37_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨299, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field37_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value37_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field37_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨300, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field37_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value37_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field37_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨301, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field37_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value37_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field37_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨302, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field37_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value37_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field37_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨303, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field37_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value37_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions37, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup38
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions38).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨38, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨38, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field38_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨304, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field38_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value38_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field38_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨305, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field38_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value38_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field38_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨306, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field38_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value38_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field38_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨307, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field38_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value38_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field38_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨308, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field38_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value38_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field38_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨309, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field38_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value38_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field38_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨310, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field38_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value38_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field38_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨311, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field38_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value38_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions38, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup39
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions39).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨39, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨39, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field39_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨312, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field39_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value39_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field39_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨313, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field39_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value39_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field39_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨314, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field39_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value39_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field39_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨315, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field39_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value39_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field39_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨316, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field39_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value39_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field39_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨317, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field39_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value39_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field39_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨318, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field39_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value39_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field39_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨319, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field39_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.generic_value39_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions39, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid


end Airbender.Compiler.CleanClosedNative.KeccakUncached
