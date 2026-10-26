import Airbender.Proofs.GKRProtocol.DecoderQueryFrame
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup
import Airbender.Proofs.GKRProtocol.MaterializedNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.PackedDecoderNormalization
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.DecoderTail.SubwordMemory.Membership

namespace Airbender.Compiler.DecoderQueryNative.SubwordMemoryUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def expressions : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression9]

theorem payload_inventory : expressions.toList = Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.payloadExpressions := by rfl

noncomputable def values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Vector Source.BaseField 9 := expressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data))

theorem normalization_geometry (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields subwordSetup (values physical data) =
      activeQuery ((decoderExpressions Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data))) := by
  apply Vector.ext
  intro column bound
  interval_cases column <;>
    simp [normalizeDecoderFields, values, expressions, activeQuery, decoderExpressions, _root_.Expression.eval,
      Airbender.SubwordMemory.importedConstraintsTraceColumns, Airbender.SubwordMemory.importedConstraintsDecoderColumns,
      subwordSetup, subwordDecoderDataColumnsMask, subwordDecoderDataTagged,
      Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression9]

theorem normalized_values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields subwordSetup (values physical data) =
      activeQuery (Trace.nativeDecoderQuery Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns
        (fun index => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get index)) :=
  (normalization_geometry physical data).trans
    (congrArg activeQuery (decoder_expressions_value Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data)))

theorem source_payload (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0) :
    (values physical data).toList = Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)) := by
  rw [values, Vector.toList_map, payload_inventory]
  exact Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.payload_fields physical data arithmetic

theorem program_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (present : (Airbender.Compiler.DecoderTail.SubwordMemory.Membership.nativeSetup.imported.data.table "Airbender.Native.SubwordMemory").Contains #[] (values physical data)) :
    (Trace.decoderTable pooledProgram .subwordMemory).Contains #[]
      (Trace.nativeDecoderQuery Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get index)) := by
  exact Airbender.Compiler.DecoderTail.SubwordMemory.Membership.lookup_sound capacity (values physical data) _ typed (normalized_values physical data) present

theorem program_from_source_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (member : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns
      (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)))) :
    (Trace.decoderTable pooledProgram .subwordMemory).Contains #[]
      (Trace.nativeDecoderQuery Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get index)) := by
  have columns : Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns = (List.range 9).map SourceSetupColumn.generic := by decide +kernel
  have payload := source_payload physical data arithmetic
  rw [← payload] at member
  have present := Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.generic_clean_contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns columns (values physical data) member "Airbender.Native.SubwordMemory" #[]
  exact program_membership capacity physical data typed present

theorem decoder_query_member : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12 ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries := by
  have same : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.get ⟨2, by decide⟩ = Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12 := by rfl
  exact same ▸ List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries ⟨2, by decide⟩

theorem program_from_framed_source (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputs.length → Source.BaseField) (counts : Fin Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.assigned (Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (enabled : (Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression0).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data) ≠ 0)
    (valid : Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.AuthoredLookupValid sourceValue) :
    (Trace.decoderTable pooledProgram .subwordMemory).Contains #[]
      (Trace.nativeDecoderQuery Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get index)) := by
  have framed : ∀ field ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.usedFields, field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) = field.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.originalProjection) := by
    intro field included
    apply Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields_preserved sourceValue counts physical inputAgreement field
    exact List.mem_flatMap.mpr ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12, List.mem_append_left _ decoder_query_member, included⟩
  have weight := decoder_weight_congr Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12 _ _ framed
  rw [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.execute_weight physical data arithmetic] at weight
  have nonzero : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.originalProjection) ≠ 0 := by
    rw [← weight]
    exact enabled
  have present := valid.1 _ decoder_query_member nonzero
  have payload := decoder_fields_congr Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12 _ _ framed
  have moved := (congrArg (fun fields => Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns fields) payload).mpr present
  exact program_from_source_membership capacity physical data arithmetic typed moved

end Airbender.Compiler.DecoderQueryNative.SubwordMemoryUncached
