import GKRProtocol.DecoderQueryFrame
import GKRProtocol.MaterializedWitnessNative.WordMemoryCached
import GKRProtocol.CleanGenericSetup
import GKRProtocol.MaterializedNative.WordMemoryCached
import GKRProtocol.PackedDecoderNormalization
import GKRProtocol.DecoderArgumentsNative.WordMemoryCached
import GKRProtocol.DecoderTail.WordMemory.Membership

namespace Airbender.Compiler.DecoderQueryNative.WordMemoryCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def expressions : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression9]

theorem payload_inventory : expressions.toList = Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.payloadExpressions := by rfl

noncomputable def values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Vector Source.BaseField 9 := expressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data))

theorem normalization_geometry (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields wordMemorySetup (values physical data) =
      activeQuery ((decoderExpressions Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data))) := by
  apply Vector.ext
  intro column bound
  interval_cases column <;>
    simp [normalizeDecoderFields, values, expressions, activeQuery, decoderExpressions, _root_.Expression.eval,
      Airbender.WordMemory.importedConstraintsTraceColumns, Airbender.WordMemory.importedConstraintsDecoderColumns,
      wordMemorySetup, wordDecoderDataColumnsMask, wordDecoderDataTagged,
      Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression9]

theorem normalized_values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    normalizeDecoderFields wordMemorySetup (values physical data) =
      activeQuery (Trace.nativeDecoderQuery Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns
        (fun index => (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data).get index)) :=
  (normalization_geometry physical data).trans
    (congrArg activeQuery (decoder_expressions_value Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data)))

theorem source_payload (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0) :
    (values physical data).toList = Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)) := by
  rw [values, Vector.toList_map, payload_inventory]
  exact Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.payload_fields physical data arithmetic

theorem program_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data).get Airbender.WordMemory.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (present : (Airbender.Compiler.DecoderTail.WordMemory.Membership.nativeSetup.imported.data.table "Airbender.Native.WordMemory").Contains #[] (values physical data)) :
    (Trace.decoderTable pooledProgram .wordMemory).Contains #[]
      (Trace.nativeDecoderQuery Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data).get index)) := by
  exact Airbender.Compiler.DecoderTail.WordMemory.Membership.lookup_sound capacity (values physical data) _ typed (normalized_values physical data) present

theorem program_from_source_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data).get Airbender.WordMemory.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (member : Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.Contains Airbender.Compiler.TableNative.WordMemoryCached.native.genericSetupColumns
      (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)))) :
    (Trace.decoderTable pooledProgram .wordMemory).Contains #[]
      (Trace.nativeDecoderQuery Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data).get index)) := by
  have columns : Airbender.Compiler.TableNative.WordMemoryCached.native.genericSetupColumns = (List.range 9).map SourceSetupColumn.generic := by decide +kernel
  have payload := source_payload physical data arithmetic
  rw [← payload] at member
  have present := Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.generic_clean_contains Airbender.Compiler.TableNative.WordMemoryCached.native.genericSetupColumns columns (values physical data) member "Airbender.Native.WordMemory" #[]
  exact program_membership capacity physical data typed present

theorem decoder_query_member : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10 ∈ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries := by
  have same : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.get ⟨1, by decide⟩ = Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10 := by rfl
  exact same ▸ List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries ⟨1, by decide⟩

theorem program_from_framed_source (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputs.length → Source.BaseField) (counts : Fin Airbender.Compiler.TableNative.WordMemoryCached.native.multiplicityColumns.length → Source.BaseField)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (inputAgreement : ∀ wire, physical (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.WordMemoryCached.native.assigned (Airbender.Compiler.HelperValidityNative.WordMemoryCached.native.canonical sourceValue) counts wire)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0)
    (typed : ((Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data).get Airbender.WordMemory.importedConstraintsTraceColumns.initialPC[0]).val < 65536)
    (enabled : (Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression0).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) ≠ 0)
    (valid : Airbender.Compiler.MaterializedWitnessNative.WordMemoryCached.AuthoredLookupValid sourceValue) :
    (Trace.decoderTable pooledProgram .wordMemory).Contains #[]
      (Trace.nativeDecoderQuery Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns (fun index => (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data).get index)) := by
  have framed : ∀ field ∈ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.usedFields, field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) = field.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.originalProjection) := by
    intro field included
    apply Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.fields_preserved sourceValue counts physical inputAgreement field
    exact List.mem_flatMap.mpr ⟨Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10, List.mem_append_left _ decoder_query_member, included⟩
  have weight := decoder_weight_congr Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10 _ _ framed
  rw [Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.execute_weight physical data arithmetic] at weight
  have nonzero : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.originalProjection) ≠ 0 := by
    rw [← weight]
    exact enabled
  have present := valid.1 _ decoder_query_member nonzero
  have payload := decoder_fields_congr Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10 _ _ framed
  have moved := (congrArg (fun fields => Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.Contains Airbender.Compiler.TableNative.WordMemoryCached.native.genericSetupColumns fields) payload).mpr present
  exact program_from_source_membership capacity physical data arithmetic typed moved

end Airbender.Compiler.DecoderQueryNative.WordMemoryCached
