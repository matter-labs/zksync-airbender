import Airbender.Proofs.GKRProtocol.CleanClosedParts.BlakeRoundUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup96
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions96).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨96, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨96, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨576, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value96_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨577, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value96_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨578, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value96_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨579, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value96_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨580, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value96_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨581, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field96_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value96_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions96, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression96_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression96_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression96_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression96_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression96_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression96_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup97
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions97).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨97, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨97, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨582, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value97_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨583, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value97_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨584, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value97_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨585, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value97_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨586, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value97_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨587, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field97_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value97_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions97, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression97_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression97_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression97_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression97_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression97_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression97_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup98
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions98).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨98, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨98, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨588, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value98_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨589, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value98_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨590, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value98_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨591, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value98_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨592, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value98_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨593, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field98_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value98_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions98, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression98_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression98_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression98_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression98_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression98_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression98_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup99
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions99).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨99, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨99, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨594, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value99_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨595, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value99_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨596, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value99_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨597, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value99_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨598, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value99_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨599, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field99_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value99_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions99, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression99_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression99_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression99_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression99_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression99_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression99_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup100
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions100).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨100, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨100, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨600, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value100_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨601, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value100_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨602, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value100_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨603, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value100_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨604, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value100_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨605, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field100_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value100_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions100, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression100_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression100_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression100_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression100_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression100_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression100_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup101
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions101).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨101, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨101, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨606, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value101_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨607, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value101_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨608, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value101_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨609, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value101_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨610, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value101_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨611, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field101_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value101_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions101, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression101_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression101_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression101_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression101_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression101_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression101_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup102
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions102).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨102, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨102, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨612, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value102_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨613, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value102_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨614, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value102_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨615, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value102_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨616, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value102_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨617, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field102_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value102_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions102, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression102_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression102_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression102_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression102_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression102_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression102_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup103
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions103).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨103, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨103, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨618, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value103_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨619, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value103_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨620, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value103_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨621, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value103_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨622, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value103_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨623, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field103_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.generic_value103_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions103, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression103_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression103_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression103_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression103_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression103_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part12.genericExpression103_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
