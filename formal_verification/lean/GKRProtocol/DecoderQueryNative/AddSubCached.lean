import GKRProtocol.DecoderQueryFrame
import GKRProtocol.MaterializedWitnessNative.AddSubCached
import GKRProtocol.CleanGenericSetup
import GKRProtocol.MaterializedNative.AddSubCached
import GKRProtocol.PackedDecoderNormalization
import GKRProtocol.DecoderArgumentsNative.AddSubCached
import GKRProtocol.DecoderTail.AddSub.Membership

namespace Airbender.Compiler.DecoderQueryNative.AddSubCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def expressions : Vector (_root_.Expression Source.BaseField) 8 :=
  #v[Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression8]

theorem payload_inventory : expressions.toList = Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.payloadExpressions := by rfl

noncomputable def values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Vector Source.BaseField 8 := expressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data))

theorem normalization_geometry (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields addSubSetup (values physical data) =
      activeQuery ((decoderExpressions Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data))) := by
  apply Vector.ext
  intro column bound
  interval_cases column <;>
    simp [normalizeDecoderFields, values, expressions, activeQuery, decoderExpressions, _root_.Expression.eval,
      Airbender.AddSub.importedConstraintsTraceColumns, Airbender.AddSub.importedConstraintsDecoderColumns,
      addSubSetup, addSubDecoderDataColumnsMask, addSubDecoderDataTagged,
      Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression8]

theorem normalized_values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields addSubSetup (values physical data) =
      activeQuery (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns
        (fun index => (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get index)) :=
  (normalization_geometry physical data).trans
    (congrArg activeQuery (decoder_expressions_value Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data)))

theorem source_payload (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (values physical data).toList = Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)) := by
  rw [values, Vector.toList_map, payload_inventory]
  exact Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.payload_fields physical data arithmetic

theorem program_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (present : (Airbender.Compiler.DecoderTail.AddSub.Membership.nativeSetup.imported.data.table "Airbender.Native.AddSub").Contains #[] (values physical data)) :
    (Trace.decoderTable pooledProgram .addSub).Contains #[]
      (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get index)) := by
  exact Airbender.Compiler.DecoderTail.AddSub.Membership.lookup_sound capacity (values physical data) _ typed (normalized_values physical data) present

theorem program_from_source_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (member : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains Airbender.Compiler.TableNative.AddSubCached.native.genericSetupColumns
      (Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)))) :
    (Trace.decoderTable pooledProgram .addSub).Contains #[]
      (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get index)) := by
  have columns : Airbender.Compiler.TableNative.AddSubCached.native.genericSetupColumns = (List.range 8).map SourceSetupColumn.generic := by decide +kernel
  have payload := source_payload physical data arithmetic
  rw [← payload] at member
  have present := Airbender.Compiler.MaterializedNative.AddSubCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.AddSubCached.native.genericSetupColumns columns (values physical data) member "Airbender.Native.AddSub" #[]
  exact program_membership capacity physical data typed present

theorem decoder_query_member : Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14 ∈ Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries := by
  have same : Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries.get ⟨0, by decide⟩ = Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14 := by rfl
  exact same ▸ List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries ⟨0, by decide⟩

theorem program_from_framed_source (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputs.length → Source.BaseField) (counts : Fin Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubCached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (enabled : (Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression0).eval (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) ≠ 0)
    (valid : Airbender.Compiler.MaterializedWitnessNative.AddSubCached.AuthoredLookupValid sourceValue) :
    (Trace.decoderTable pooledProgram .addSub).Contains #[]
      (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get index)) := by
  have framed : ∀ field ∈ Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.usedFields, field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) = field.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection) := by
    intro field included
    apply Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields_preserved sourceValue counts physical inputAgreement field
    exact List.mem_flatMap.mpr ⟨Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14, List.mem_append_left _ decoder_query_member, included⟩
  have weight := decoder_weight_congr Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14 _ _ framed
  rw [Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.execute_weight physical data arithmetic] at weight
  have nonzero : Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection) ≠ 0 := by
    rw [← weight]
    exact enabled
  have present := valid.1 _ decoder_query_member nonzero
  have payload := decoder_fields_congr Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14 _ _ framed
  have moved := (congrArg (fun fields => Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains Airbender.Compiler.TableNative.AddSubCached.native.genericSetupColumns fields) payload).mpr present
  exact program_from_source_membership capacity physical data arithmetic typed moved

end Airbender.Compiler.DecoderQueryNative.AddSubCached
