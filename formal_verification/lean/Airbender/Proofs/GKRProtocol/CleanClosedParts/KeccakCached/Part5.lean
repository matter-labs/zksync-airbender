import Airbender.Proofs.GKRProtocol.CleanClosedParts.KeccakCached.Shared

namespace Airbender.Compiler.CleanClosedNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup40
    (sourceValue : Fin 266 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.KeccakCached.native.assigned (Airbender.Compiler.HelperValidityNative.KeccakCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.KeccakCached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions40).Contains (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.get ⟨40, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries ⟨40, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.KeccakCached.native.field40_0.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨320, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field40_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.generic_value40_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.KeccakCached.native.field40_1.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨321, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field40_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.generic_value40_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.KeccakCached.native.field40_2.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨322, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field40_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.generic_value40_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.KeccakCached.native.field40_3.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨323, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field40_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.generic_value40_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.KeccakCached.native.field40_4.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨324, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field40_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.generic_value40_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.KeccakCached.native.field40_5.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨325, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field40_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.generic_value40_5 physical data arithmetic).trans transported5
  have present6 : Airbender.Compiler.LookupNative.KeccakCached.native.field40_6.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨326, by decide⟩
  have transported6 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field40_6.source present6
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.generic_value40_6 physical data arithmetic).trans transported6
  have present7 : Airbender.Compiler.LookupNative.KeccakCached.native.field40_7.source ∈ Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields ⟨327, by decide⟩
  have transported7 := Airbender.Compiler.QueryFrameNative.KeccakCached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.KeccakCached.native.field40_7.source present7
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.generic_value40_7 physical data arithmetic).trans transported7
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.KeccakCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Keccak" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions40, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.KeccakCached.native.model.Contains Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.genericExpression40_0.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.genericExpression40_1.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.genericExpression40_2.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.genericExpression40_3.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.genericExpression40_4.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.genericExpression40_5.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.genericExpression40_6.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.part5.genericExpression40_7.eval (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5, same6, same7]
  exact valid


end Airbender.Compiler.CleanClosedNative.KeccakCached
