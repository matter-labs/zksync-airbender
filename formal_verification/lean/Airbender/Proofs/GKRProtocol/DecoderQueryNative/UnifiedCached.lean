import Airbender.Proofs.GKRProtocol.DecoderQueryFrame
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup
import Airbender.Proofs.GKRProtocol.MaterializedNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.PackedDecoderNormalization
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.DecoderTail.Unified.Membership

namespace Airbender.Compiler.DecoderQueryNative.UnifiedCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def expressions : Vector (_root_.Expression Source.BaseField) 10 :=
  #v[Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression10]

theorem payload_inventory : expressions.toList = Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.payloadExpressions := by rfl

noncomputable def values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Vector Source.BaseField 10 := expressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data))

theorem normalization_geometry (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields unifiedSetup (values physical data) =
      activeQuery ((decoderExpressions Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data))) := by
  apply Vector.ext
  intro column bound
  interval_cases column <;>
    simp [normalizeDecoderFields, values, expressions, activeQuery, _root_.Expression.eval,
      unifiedSetup, unifiedDecoderDataColumnsMask, unifiedDecoderDataTagged,
      Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression10]

theorem normalized_values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields unifiedSetup (values physical data) =
      activeQuery (Trace.nativeDecoderQuery Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns
        (fun index => (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data).get index)) :=
  (normalization_geometry physical data).trans
    (congrArg activeQuery (decoder_expressions_value Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)))

theorem source_payload (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (values physical data).toList = Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)) := by
  rw [values, Vector.toList_map, payload_inventory]
  exact Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.payload_fields physical data arithmetic

theorem program_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data).get Airbender.UnifiedReduced.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (present : (Airbender.Compiler.DecoderTail.Unified.Membership.nativeSetup.imported.data.table "Airbender.Native.UnifiedReduced").Contains #[] (values physical data)) :
    (Trace.decoderTable unifiedProgram .machine).Contains #[]
      (Trace.nativeDecoderQuery Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data).get index)) := by
  have identity := Airbender.Compiler.DecoderTail.Unified.Rows.normalize_fields_identity (values physical data)
  have same := identity.symm.trans (normalized_values physical data)
  rw [same] at present
  exact Airbender.Compiler.DecoderTail.Unified.Membership.lookup_sound capacity _ typed present

theorem program_from_source_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data).get Airbender.UnifiedReduced.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (member : Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns
      (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)))) :
    (Trace.decoderTable unifiedProgram .machine).Contains #[]
      (Trace.nativeDecoderQuery Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data).get index)) := by
  have columns : Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns = (List.range 10).map SourceSetupColumn.generic := by decide +kernel
  have payload := source_payload physical data arithmetic
  rw [← payload] at member
  have present := Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns columns (values physical data) member "Airbender.Native.UnifiedReduced" #[]
  exact program_membership capacity physical data typed present

theorem decoder_query_member : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20 ∈ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries := by
  have same : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨5, by decide⟩ = Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20 := by rfl
  exact same ▸ List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨5, by decide⟩

theorem program_from_framed_source (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputs.length → Source.BaseField) (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data).get Airbender.UnifiedReduced.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (enabled : (Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression0).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) ≠ 0)
    (valid : Airbender.Compiler.MaterializedWitnessNative.UnifiedCached.AuthoredLookupValid sourceValue) :
    (Trace.decoderTable unifiedProgram .machine).Contains #[]
      (Trace.nativeDecoderQuery Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data).get index)) := by
  have framed : ∀ field ∈ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.usedFields, field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) = field.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) := by
    intro field included
    apply Airbender.Compiler.QueryFrameNative.UnifiedCached.native.fields_preserved sourceValue counts physical inputAgreement field
    exact List.mem_flatMap.mpr ⟨Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20, List.mem_append_left _ decoder_query_member, included⟩
  have weight := decoder_weight_congr Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20 _ _ framed
  rw [Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.execute_weight physical data arithmetic] at weight
  have nonzero : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 := by
    rw [← weight]
    exact enabled
  have present := valid.1 _ decoder_query_member nonzero
  have payload := decoder_fields_congr Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20 _ _ framed
  have moved := (congrArg (fun fields => Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns fields) payload).mpr present
  exact program_from_source_membership capacity physical data arithmetic typed moved

end Airbender.Compiler.DecoderQueryNative.UnifiedCached
