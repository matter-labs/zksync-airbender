import Airbender.Proofs.GKRProtocol.DecoderQueryFrame
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup
import Airbender.Proofs.GKRProtocol.MaterializedNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.PackedDecoderNormalization
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Membership

namespace Airbender.Compiler.DecoderQueryNative.ShiftBinopCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def expressions : Vector (_root_.Expression Source.BaseField) 10 :=
  #v[Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression10]

theorem payload_inventory : expressions.toList = Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.payloadExpressions := by rfl

noncomputable def values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Vector Source.BaseField 10 := expressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data))

theorem normalization_geometry (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields shiftBinopSetup (values physical data) =
      activeQuery ((decoderExpressions Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data))) := by
  apply Vector.ext
  intro column bound
  interval_cases column <;>
    simp [normalizeDecoderFields, values, expressions, activeQuery, _root_.Expression.eval,
      shiftBinopSetup, shiftDecoderDataColumnsMask, shiftDecoderDataTagged,
      Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression10]

theorem normalized_values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields shiftBinopSetup (values physical data) =
      activeQuery (Trace.nativeDecoderQuery Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns
        (fun index => (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data).get index)) :=
  (normalization_geometry physical data).trans
    (congrArg activeQuery (decoder_expressions_value Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data)))

theorem source_payload (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0) :
    (values physical data).toList = Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)) := by
  rw [values, Vector.toList_map, payload_inventory]
  exact Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.payload_fields physical data arithmetic

theorem program_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data).get Airbender.ShiftBinop.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (present : (Airbender.Compiler.DecoderTail.ShiftBinop.Membership.nativeSetup.imported.data.table "Airbender.Native.ShiftBinop").Contains #[] (values physical data)) :
    (Trace.decoderTable pooledProgram .shiftBinop).Contains #[]
      (Trace.nativeDecoderQuery Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data).get index)) := by
  exact Airbender.Compiler.DecoderTail.ShiftBinop.Membership.lookup_sound capacity (values physical data) _ typed (normalized_values physical data) present

theorem program_from_source_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data).get Airbender.ShiftBinop.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (member : Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns
      (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)))) :
    (Trace.decoderTable pooledProgram .shiftBinop).Contains #[]
      (Trace.nativeDecoderQuery Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data).get index)) := by
  have columns : Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns = (List.range 10).map SourceSetupColumn.generic := by decide +kernel
  have payload := source_payload physical data arithmetic
  rw [← payload] at member
  have present := Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns columns (values physical data) member "Airbender.Native.ShiftBinop" #[]
  exact program_membership capacity physical data typed present

theorem decoder_query_member : Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10 ∈ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries := by
  have same : Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨5, by decide⟩ = Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10 := by rfl
  exact same ▸ List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries ⟨5, by decide⟩

theorem program_from_framed_source (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputs.length → Source.BaseField) (counts : Fin Airbender.Compiler.TableNative.ShiftBinopCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.assigned (Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data).get Airbender.ShiftBinop.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (enabled : (Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression0).eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) ≠ 0)
    (valid : Airbender.Compiler.MaterializedWitnessNative.ShiftBinopCached.AuthoredLookupValid sourceValue) :
    (Trace.decoderTable pooledProgram .shiftBinop).Contains #[]
      (Trace.nativeDecoderQuery Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data).get index)) := by
  have framed : ∀ field ∈ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.usedFields, field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) = field.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.originalProjection) := by
    intro field included
    apply Airbender.Compiler.QueryFrameNative.ShiftBinopCached.native.fields_preserved sourceValue counts physical inputAgreement field
    exact List.mem_flatMap.mpr ⟨Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10, List.mem_append_left _ decoder_query_member, included⟩
  have weight := decoder_weight_congr Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10 _ _ framed
  rw [Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.execute_weight physical data arithmetic] at weight
  have nonzero : Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.originalProjection) ≠ 0 := by
    rw [← weight]
    exact enabled
  have present := valid.1 _ decoder_query_member nonzero
  have payload := decoder_fields_congr Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10 _ _ framed
  have moved := (congrArg (fun fields => Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns fields) payload).mpr present
  exact program_from_source_membership capacity physical data arithmetic typed moved

end Airbender.Compiler.DecoderQueryNative.ShiftBinopCached
