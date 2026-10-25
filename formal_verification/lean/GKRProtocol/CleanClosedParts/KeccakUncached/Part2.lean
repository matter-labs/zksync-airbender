import GKRProtocol.CleanClosedParts.KeccakUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup16
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions16).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨16, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨16, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field16_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨128, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field16_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value16_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field16_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨129, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field16_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value16_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field16_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨130, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field16_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value16_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field16_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨131, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field16_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value16_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field16_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨132, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field16_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value16_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field16_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨133, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field16_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value16_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field16_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨134, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field16_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value16_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field16_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨135, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field16_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value16_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions16, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup17
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions17).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨17, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨17, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field17_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨136, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field17_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value17_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field17_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨137, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field17_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value17_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field17_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨138, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field17_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value17_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field17_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨139, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field17_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value17_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field17_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨140, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field17_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value17_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field17_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨141, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field17_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value17_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field17_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨142, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field17_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value17_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field17_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨143, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field17_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value17_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions17, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup18
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions18).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨18, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨18, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field18_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨144, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field18_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value18_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field18_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨145, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field18_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value18_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field18_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨146, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field18_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value18_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field18_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨147, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field18_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value18_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field18_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨148, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field18_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value18_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field18_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨149, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field18_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value18_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field18_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨150, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field18_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value18_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field18_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨151, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field18_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value18_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions18, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup19
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions19).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨19, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨19, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field19_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨152, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field19_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value19_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field19_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨153, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field19_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value19_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field19_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨154, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field19_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value19_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field19_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨155, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field19_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value19_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field19_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨156, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field19_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value19_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field19_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨157, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field19_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value19_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field19_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨158, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field19_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value19_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field19_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨159, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field19_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value19_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions19, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup20
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions20).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨20, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨20, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field20_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨160, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field20_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value20_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field20_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨161, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field20_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value20_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field20_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨162, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field20_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value20_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field20_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨163, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field20_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value20_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field20_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨164, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field20_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value20_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field20_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨165, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field20_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value20_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field20_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨166, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field20_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value20_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field20_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨167, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field20_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value20_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions20, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup21
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions21).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨21, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨21, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field21_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨168, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field21_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value21_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field21_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨169, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field21_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value21_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field21_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨170, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field21_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value21_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field21_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨171, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field21_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value21_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field21_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨172, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field21_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value21_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field21_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨173, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field21_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value21_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field21_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨174, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field21_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value21_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field21_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨175, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field21_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value21_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions21, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup22
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions22).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨22, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨22, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field22_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨176, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field22_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value22_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field22_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨177, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field22_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value22_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field22_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨178, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field22_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value22_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field22_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨179, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field22_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value22_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field22_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨180, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field22_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value22_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field22_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨181, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field22_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value22_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field22_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨182, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field22_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value22_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field22_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨183, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field22_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value22_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions22, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid

theorem generic_lookup23
    (sourceValue : Fin 267 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakUncached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions23).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries.get ⟨23, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries ⟨23, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakUncached.native.field23_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨184, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field23_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value23_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakUncached.native.field23_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨185, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field23_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value23_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakUncached.native.field23_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨186, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field23_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value23_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakUncached.native.field23_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨187, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field23_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value23_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakUncached.native.field23_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨188, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field23_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value23_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakUncached.native.field23_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨189, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field23_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value23_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakUncached.native.field23_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨190, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field23_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value23_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakUncached.native.field23_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields ⟨191, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakUncached.native.field23_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.generic_value23_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions23, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.Contains Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid


end Airbender.Compiler.CleanClosedNative.KeccakUncached
