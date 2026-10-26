import Airbender.Proofs.GKRProtocol.CleanClosedParts.BlakeRoundUncached.Shared

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem generic_lookup120
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions120).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨120, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨120, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨720, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value120_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨721, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value120_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨722, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value120_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨723, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value120_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨724, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value120_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨725, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field120_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value120_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions120, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression120_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression120_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression120_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression120_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression120_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression120_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup121
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions121).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨121, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨121, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨726, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value121_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨727, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value121_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨728, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value121_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨729, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value121_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨730, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value121_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨731, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field121_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value121_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions121, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression121_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression121_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression121_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression121_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression121_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression121_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup122
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions122).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨122, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨122, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨732, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value122_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨733, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value122_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨734, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value122_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨735, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value122_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨736, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value122_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨737, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field122_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value122_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions122, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression122_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression122_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression122_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression122_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression122_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression122_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup123
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions123).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨123, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨123, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨738, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value123_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨739, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value123_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨740, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value123_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨741, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value123_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨742, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value123_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨743, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field123_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value123_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions123, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression123_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression123_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression123_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression123_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression123_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression123_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup124
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions124).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨124, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨124, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨744, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value124_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨745, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value124_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨746, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value124_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨747, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value124_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨748, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value124_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨749, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field124_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value124_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions124, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression124_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression124_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression124_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression124_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression124_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression124_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup125
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions125).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨125, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨125, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨750, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value125_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨751, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value125_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨752, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value125_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨753, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value125_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨754, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value125_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨755, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field125_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value125_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions125, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression125_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression125_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression125_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression125_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression125_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression125_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup126
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions126).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨126, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨126, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨756, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value126_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨757, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value126_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨758, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value126_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨759, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value126_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨760, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value126_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨761, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field126_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value126_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions126, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression126_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression126_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression126_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression126_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression126_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression126_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid

theorem generic_lookup127
    (sourceValue : Fin 763 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.assigned (Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (authored : Airbender.Compiler.MaterializedWitnessNative.BlakeRoundUncached.AuthoredLookupValid sourceValue) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions127).Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries.get ⟨127, by decide⟩
  have member := authored query (List.get_mem Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries ⟨127, by decide⟩)
  have nonzero : query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.originalProjection) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have present0 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_0.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨762, by decide⟩
  have transported0 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_0.source present0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value127_0 physical data arithmetic).trans transported0
  have present1 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_1.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨763, by decide⟩
  have transported1 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_1.source present1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value127_1 physical data arithmetic).trans transported1
  have present2 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_2.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨764, by decide⟩
  have transported2 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_2.source present2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value127_2 physical data arithmetic).trans transported2
  have present3 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_3.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨765, by decide⟩
  have transported3 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_3.source present3
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value127_3 physical data arithmetic).trans transported3
  have present4 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_4.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨766, by decide⟩
  have transported4 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_4.source present4
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value127_4 physical data arithmetic).trans transported4
  have present5 : Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_5.source ∈ Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields := List.get_mem Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields ⟨767, by decide⟩
  have transported5 := Airbender.Compiler.QueryFrameNative.BlakeRoundUncached.native.fields_preserved sourceValue counts physical inputAgreement Airbender.Compiler.LookupNative.BlakeRoundUncached.native.field127_5.source present5
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.generic_value127_5 physical data arithmetic).trans transported5
  apply clean_vector_lookup
  apply Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.Blake2Round" _
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions127, Vector.map_mk, List.map_toArray]
  change Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.Contains Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression127_0.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression127_1.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression127_2.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression127_3.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression127_4.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.part15.genericExpression127_5.eval (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment physical data)]
  rw [same0, same1, same2, same3, same4, same5]
  exact valid


end Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
