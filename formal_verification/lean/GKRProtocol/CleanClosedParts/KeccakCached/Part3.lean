import GKRProtocol.CleanClosedParts.KeccakCached.Shared

namespace Airbender.Compiler.CleanClosedNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup24
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions24).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.get ⟨24, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries ⟨24, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakCached.native.field24_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨192, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field24_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value24_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakCached.native.field24_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨193, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field24_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value24_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakCached.native.field24_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨194, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field24_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value24_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakCached.native.field24_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨195, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field24_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value24_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakCached.native.field24_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨196, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field24_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value24_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakCached.native.field24_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨197, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field24_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value24_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakCached.native.field24_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨198, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field24_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value24_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakCached.native.field24_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨199, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field24_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value24_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions24, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakCached.native.model.Contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression24_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression24_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression24_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression24_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression24_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression24_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression24_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression24_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup25
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions25).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.get ⟨25, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries ⟨25, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakCached.native.field25_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨200, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field25_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value25_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakCached.native.field25_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨201, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field25_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value25_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakCached.native.field25_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨202, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field25_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value25_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakCached.native.field25_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨203, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field25_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value25_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakCached.native.field25_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨204, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field25_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value25_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakCached.native.field25_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨205, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field25_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value25_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakCached.native.field25_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨206, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field25_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value25_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakCached.native.field25_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨207, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field25_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value25_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions25, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakCached.native.model.Contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression25_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression25_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression25_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression25_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression25_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression25_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression25_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression25_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup26
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions26).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.get ⟨26, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries ⟨26, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakCached.native.field26_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨208, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field26_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value26_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakCached.native.field26_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨209, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field26_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value26_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakCached.native.field26_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨210, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field26_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value26_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakCached.native.field26_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨211, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field26_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value26_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakCached.native.field26_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨212, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field26_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value26_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakCached.native.field26_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨213, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field26_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value26_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakCached.native.field26_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨214, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field26_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value26_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakCached.native.field26_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨215, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field26_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value26_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions26, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakCached.native.model.Contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression26_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression26_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression26_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression26_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression26_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression26_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression26_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression26_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup27
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions27).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.get ⟨27, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries ⟨27, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakCached.native.field27_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨216, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field27_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value27_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakCached.native.field27_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨217, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field27_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value27_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakCached.native.field27_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨218, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field27_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value27_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakCached.native.field27_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨219, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field27_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value27_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakCached.native.field27_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨220, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field27_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value27_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakCached.native.field27_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨221, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field27_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value27_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakCached.native.field27_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨222, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field27_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value27_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakCached.native.field27_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨223, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field27_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value27_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions27, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakCached.native.model.Contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression27_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression27_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression27_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression27_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression27_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression27_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression27_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression27_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup28
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions28).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.get ⟨28, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries ⟨28, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakCached.native.field28_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨224, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field28_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value28_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakCached.native.field28_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨225, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field28_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value28_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakCached.native.field28_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨226, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field28_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value28_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakCached.native.field28_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨227, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field28_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value28_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakCached.native.field28_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨228, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field28_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value28_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakCached.native.field28_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨229, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field28_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value28_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakCached.native.field28_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨230, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field28_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value28_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakCached.native.field28_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨231, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field28_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value28_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions28, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakCached.native.model.Contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression28_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression28_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression28_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression28_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression28_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression28_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression28_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression28_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup29
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions29).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.get ⟨29, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries ⟨29, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakCached.native.field29_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨232, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field29_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value29_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakCached.native.field29_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨233, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field29_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value29_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakCached.native.field29_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨234, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field29_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value29_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakCached.native.field29_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨235, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field29_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value29_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakCached.native.field29_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨236, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field29_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value29_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakCached.native.field29_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨237, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field29_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value29_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakCached.native.field29_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨238, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field29_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value29_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakCached.native.field29_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨239, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field29_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value29_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions29, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakCached.native.model.Contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression29_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression29_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression29_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression29_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression29_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression29_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression29_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression29_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup30
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions30).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.get ⟨30, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries ⟨30, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakCached.native.field30_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨240, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field30_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value30_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakCached.native.field30_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨241, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field30_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value30_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakCached.native.field30_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨242, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field30_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value30_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakCached.native.field30_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨243, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field30_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value30_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakCached.native.field30_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨244, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field30_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value30_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakCached.native.field30_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨245, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field30_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value30_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakCached.native.field30_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨246, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field30_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value30_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakCached.native.field30_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨247, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field30_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value30_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions30, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakCached.native.model.Contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression30_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression30_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression30_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression30_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression30_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression30_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression30_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression30_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup31
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions31).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.get ⟨31, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries ⟨31, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakCached.native.field31_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨248, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field31_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value31_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakCached.native.field31_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨249, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field31_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value31_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakCached.native.field31_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨250, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field31_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value31_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakCached.native.field31_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨251, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field31_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value31_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakCached.native.field31_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨252, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field31_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value31_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakCached.native.field31_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨253, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field31_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value31_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakCached.native.field31_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨254, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field31_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value31_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakCached.native.field31_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨255, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field31_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.generic_value31_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions31, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakCached.native.model.Contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression31_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression31_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression31_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression31_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression31_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression31_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression31_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part3.genericExpression31_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid


end Airbender.Compiler.CleanClosedNative.KeccakCached
