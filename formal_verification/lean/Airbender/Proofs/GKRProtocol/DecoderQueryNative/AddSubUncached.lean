import Airbender.Proofs.GKRProtocol.DecoderQueryFrame
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup
import Airbender.Proofs.GKRProtocol.MaterializedNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.PackedDecoderNormalization
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.DecoderTail.AddSub.Membership

namespace Airbender.Compiler.DecoderQueryNative.AddSubUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def expressions : Vector (_root_.Expression Source.BaseField) 8 :=
  #v[Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression8]

theorem payload_inventory : expressions.toList = Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.payloadExpressions := by rfl

noncomputable def values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Vector Source.BaseField 8 := expressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data))

theorem normalization_geometry (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields addSubSetup (values physical data) =
      activeQuery ((decoderExpressions Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data))) := by
  apply Vector.ext
  intro column bound
  interval_cases column <;>
    simp [normalizeDecoderFields, values, expressions, activeQuery, decoderExpressions, _root_.Expression.eval,
      Airbender.AddSub.importedConstraintsTraceColumns, Airbender.AddSub.importedConstraintsDecoderColumns,
      addSubSetup, addSubDecoderDataColumnsMask, addSubDecoderDataTagged,
      Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression8]

theorem normalized_values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields addSubSetup (values physical data) =
      activeQuery (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns
        (fun index => (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data).get index)) :=
  (normalization_geometry physical data).trans
    (congrArg activeQuery (decoder_expressions_value Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data)))

theorem source_payload (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0) :
    (values physical data).toList = Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)) := by
  rw [values, Vector.toList_map, payload_inventory]
  exact Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.payload_fields physical data arithmetic

theorem program_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (present : (Airbender.Compiler.DecoderTail.AddSub.Membership.nativeSetup.imported.data.table "Airbender.Native.AddSub").Contains #[] (values physical data)) :
    (Trace.decoderTable pooledProgram .addSub).Contains #[]
      (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data).get index)) := by
  exact Airbender.Compiler.DecoderTail.AddSub.Membership.lookup_sound capacity (values physical data) _ typed (normalized_values physical data) present

theorem program_from_source_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (member : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains Airbender.Compiler.TableNative.AddSubUncached.native.genericSetupColumns
      (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)))) :
    (Trace.decoderTable pooledProgram .addSub).Contains #[]
      (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data).get index)) := by
  have columns : Airbender.Compiler.TableNative.AddSubUncached.native.genericSetupColumns = (List.range 8).map SourceSetupColumn.generic := by decide +kernel
  have payload := source_payload physical data arithmetic
  rw [← payload] at member
  have present := Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.AddSubUncached.native.genericSetupColumns columns (values physical data) member "Airbender.Native.AddSub" #[]
  exact program_membership capacity physical data typed present

theorem decoder_query_member : Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14 ∈ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.genericQueries := by
  have same : Airbender.Compiler.LookupSourceNative.AddSubUncached.native.genericQueries.get ⟨0, by decide⟩ = Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14 := by rfl
  exact same ▸ List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.genericQueries ⟨0, by decide⟩

theorem program_from_framed_source (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputs.length → Source.BaseField) (counts : Fin Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.AddSubUncached.native.assigned (Airbender.Compiler.HelperValidityNative.AddSubUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (enabled : (Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression0).eval (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data) ≠ 0)
    (valid : Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.AuthoredLookupValid sourceValue) :
    (Trace.decoderTable pooledProgram .addSub).Contains #[]
      (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment physical data).get index)) := by
  have framed : ∀ field ∈ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14.usedFields, field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) = field.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection) := by
    intro field included
    apply Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields_preserved sourceValue counts physical inputAgreement field
    exact List.mem_flatMap.mpr ⟨Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14, List.mem_append_left _ decoder_query_member, included⟩
  have weight := decoder_weight_congr Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14 _ _ framed
  rw [Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.execute_weight physical data arithmetic] at weight
  have nonzero : Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection) ≠ 0 := by
    rw [← weight]
    exact enabled
  have present := valid.1 _ decoder_query_member nonzero
  have payload := decoder_fields_congr Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14 _ _ framed
  have moved := (congrArg (fun fields => Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains Airbender.Compiler.TableNative.AddSubUncached.native.genericSetupColumns fields) payload).mpr present
  exact program_from_source_membership capacity physical data arithmetic typed moved

end Airbender.Compiler.DecoderQueryNative.AddSubUncached
