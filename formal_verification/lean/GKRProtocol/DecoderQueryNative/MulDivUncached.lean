import GKRProtocol.DecoderQueryFrame
import GKRProtocol.MaterializedWitnessNative.MulDivUncached
import GKRProtocol.CleanGenericSetup
import GKRProtocol.MaterializedNative.MulDivUncached
import GKRProtocol.PackedDecoderNormalization
import GKRProtocol.DecoderArgumentsNative.MulDivUncached
import GKRProtocol.DecoderTail.MulDiv.Membership

namespace Airbender.Compiler.DecoderQueryNative.MulDivUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def expressions : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression9]

theorem payload_inventory : expressions.toList = Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.payloadExpressions := by rfl

noncomputable def values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Vector Source.BaseField 9 := expressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data))

theorem normalization_geometry (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields mulDivSetup (values physical data) =
      activeQuery ((decoderExpressions Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data))) := by
  apply Vector.ext
  intro column bound
  interval_cases column <;>
    simp [normalizeDecoderFields, values, expressions, activeQuery, decoderExpressions, _root_.Expression.eval,
      Airbender.MulDiv.importedConstraintsTraceColumns, Airbender.MulDiv.importedConstraintsDecoderColumns,
      mulDivSetup, mulDivDecoderDataColumnsMask, mulDivDecoderDataTagged,
      Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression9]

theorem normalized_values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields mulDivSetup (values physical data) =
      activeQuery (Trace.nativeDecoderQuery Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns
        (fun index => (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data).get index)) :=
  (normalization_geometry physical data).trans
    (congrArg activeQuery (decoder_expressions_value Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data)))

theorem source_payload (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address) = 0) :
    (values physical data).toList = Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)) := by
  rw [values, Vector.toList_map, payload_inventory]
  exact Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.payload_fields physical data arithmetic

theorem program_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (present : (Airbender.Compiler.DecoderTail.MulDiv.Membership.nativeSetup.imported.data.table "Airbender.Native.MulDiv").Contains #[] (values physical data)) :
    (Trace.decoderTable pooledProgram .mulDiv).Contains #[]
      (Trace.nativeDecoderQuery Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data).get index)) := by
  exact Airbender.Compiler.DecoderTail.MulDiv.Membership.lookup_sound capacity (values physical data) _ typed (normalized_values physical data) present

theorem program_from_source_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (member : Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains Airbender.Compiler.TableNative.MulDivUncached.native.genericSetupColumns
      (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)))) :
    (Trace.decoderTable pooledProgram .mulDiv).Contains #[]
      (Trace.nativeDecoderQuery Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data).get index)) := by
  have columns : Airbender.Compiler.TableNative.MulDivUncached.native.genericSetupColumns = (List.range 9).map SourceSetupColumn.generic := by decide +kernel
  have payload := source_payload physical data arithmetic
  rw [← payload] at member
  have present := Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.MulDivUncached.native.genericSetupColumns columns (values physical data) member "Airbender.Native.MulDiv" #[]
  exact program_membership capacity physical data typed present

theorem decoder_query_member : Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16 ∈ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries := by
  have same : Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.get ⟨8, by decide⟩ = Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16 := by rfl
  exact same ▸ List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨8, by decide⟩

theorem program_from_framed_source (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputs.length → Source.BaseField) (counts : Fin Airbender.Compiler.TableNative.MulDivUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.MulDivUncached.native.assigned (Airbender.Compiler.HelperValidityNative.MulDivUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (enabled : (Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression0).eval (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data) ≠ 0)
    (valid : Airbender.Compiler.MaterializedWitnessNative.MulDivUncached.AuthoredLookupValid sourceValue) :
    (Trace.decoderTable pooledProgram .mulDiv).Contains #[]
      (Trace.nativeDecoderQuery Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment physical data).get index)) := by
  have framed : ∀ field ∈ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16.usedFields, field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = field.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.originalProjection) := by
    intro field included
    apply Airbender.Compiler.QueryFrameNative.MulDivUncached.native.fields_preserved sourceValue counts physical inputAgreement field
    exact List.mem_flatMap.mpr ⟨Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16, List.mem_append_left _ decoder_query_member, included⟩
  have weight := decoder_weight_congr Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16 _ _ framed
  rw [Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.execute_weight physical data arithmetic] at weight
  have nonzero : Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.originalProjection) ≠ 0 := by
    rw [← weight]
    exact enabled
  have present := valid.1 _ decoder_query_member nonzero
  have payload := decoder_fields_congr Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16 _ _ framed
  have moved := (congrArg (fun fields => Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains Airbender.Compiler.TableNative.MulDivUncached.native.genericSetupColumns fields) payload).mpr present
  exact program_from_source_membership capacity physical data arithmetic typed moved

end Airbender.Compiler.DecoderQueryNative.MulDivUncached
