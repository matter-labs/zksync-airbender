import GKRProtocol.CleanArguments
import Airbender.Review.Helpers.Decoder.Program
import Mathlib.Algebra.BigOperators.Fin

namespace Airbender.Compiler
set_option warningAsError true

private def decoderFlagFold (columns : Trace.DecoderColumns)
    (indices : List (Fin columns.flags.size)) : _root_.Expression Source.BaseField :=
  indices.foldr (fun index rest =>
    .add (.mul (.const ((2 ^ index.val : Nat) : Source.BaseField))
      (.var ⟨columns.flags[index]⟩)) rest) (.const 0)

def decoderFlagExpression (columns : Trace.DecoderColumns) : _root_.Expression Source.BaseField :=
  decoderFlagFold columns (List.finRange columns.flags.size)

def decoderExpressions (trace : Trace.TraceColumns) (columns : Trace.DecoderColumns) :
    Vector (_root_.Expression Source.BaseField) 9 :=
  #v[.var ⟨trace.initialPC[0]⟩, .var ⟨trace.initialPC[1]⟩,
    .var ⟨columns.rs1⟩, .var ⟨columns.rs2⟩, .var ⟨columns.rd⟩,
    .var ⟨columns.immediate[0]⟩, .var ⟨columns.immediate[1]⟩,
    (columns.funct3.map (fun index => .var ⟨index⟩)).getD (.const 0),
    decoderFlagExpression columns]

private theorem decoder_flag_fold_value (columns : Trace.DecoderColumns)
    (indices : List (Fin columns.flags.size)) (environment : Environment Source.BaseField) :
    (decoderFlagFold columns indices).eval environment =
      (indices.map (fun index => ((2 ^ index.val : Nat) : Source.BaseField) *
        environment.get columns.flags[index])).sum := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [decoderFlagFold, List.foldr_cons, List.map_cons, List.sum_cons,
      _root_.Expression.eval] at *
    exact congrArg (fun tail => ((2 ^ index.val : Nat) : Source.BaseField) *
      environment.get columns.flags[index] + tail) ih

theorem decoder_flag_expression_value (columns : Trace.DecoderColumns)
    (environment : Environment Source.BaseField) :
    (decoderFlagExpression columns).eval environment =
      ∑ index : Fin columns.flags.size,
        ((2 ^ index.val : Nat) : Source.BaseField) * environment.get columns.flags[index] := by
  rw [decoderFlagExpression, decoder_flag_fold_value, ← List.ofFn_eq_map, List.sum_ofFn]

theorem decoder_expressions_value (trace : Trace.TraceColumns) (columns : Trace.DecoderColumns)
    (environment : Environment Source.BaseField) :
    (decoderExpressions trace columns).map (fun expression => expression.eval environment) =
      Trace.nativeDecoderQuery trace columns (fun index => environment.get index) := by
  apply Vector.ext
  intro index bound
  simp only [Vector.getElem_map]
  interval_cases index
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases selected : columns.funct3 <;>
      simp [decoderExpressions, Trace.nativeDecoderQuery, selected, _root_.Expression.eval]
  · exact decoder_flag_expression_value columns environment

theorem source_query_weight_hom {R : Type} [CommRing R] (query : SourceLookupQuery)
    (hom : Source.BaseField →+* R) (values : Nat → Source.BaseField) :
    query.weight hom values = hom (query.weight (RingHom.id _) values) := by
  cases selected : query.mask <;> simp [SourceLookupQuery.weight, selected]

end Airbender.Compiler
