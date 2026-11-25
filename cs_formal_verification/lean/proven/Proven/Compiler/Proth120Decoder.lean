module
import all Mathlib.Data.List.Sort
public import Proven.Compiler.Proth120Native

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Compiler.Proth120Native
set_option maxRecDepth 32768

private def sumExpr (es : List (Expression F)) : Expression F := es.foldr .add (.const 0)

private noncomputable def decoderExpressions : List (Expression F) :=
  let c := importedConstraintsDecoderColumns
  let pc := importedConstraintsTraceColumns.initialPC
  let v := fun i => Expression.var (F := F) ⟨i⟩
  let mask := sumExpr (List.ofFn fun i : Fin c.flags.size =>
    Expression.mul (.const ((2^i.val : Nat) : F)) (v c.flags[i]))
  [v pc[0], v pc[1], v c.rs1, v c.rs2, v c.rd, v c.immediate[0], v c.immediate[1],
   (c.funct3.map v).getD (.const 0), mask, .const 46]

private theorem evalDecoder (w : Nat → F) :
    decoderExpressions.map (fun e => e.eval (Verification.environment w)) =
      (Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w).toList ++ [46] := by
  simp only [decoderExpressions, List.map_cons, List.map_nil,
    Expression.eval, Verification.environment, Trace.nativeDecoderQuery]
  rfl

theorem native_decoder_holds {setup : Table F (fields 10)} {decode} {rows : PublicLookupRows setup decode}
    {physical logical} (native : NativeArithmetic physical logical) (matched : NativeLookupsMatched rows.generic physical)
    (active : logical importedConstraintsTraceColumns.execute = 1) :
    decode (Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns logical) := by
  let q := nativeQueries[20]
  have binding : fieldsCheck nativeCoordinates nativeScalar placements decoderExpressions q.fields = true := by kernel_rfl
  have placed := native.2 (4, .BaseLayerMemory 21) (by decide +kernel)
  have enabled : (q.enable.map physical).getD 1 ≠ 0 := by
    change physical (.BaseLayerMemory 21) ≠ 0
    rw [← placed]
    exact active ▸ one_ne_zero
  have mem := matched q (List.getElem_mem _) enabled
  apply rows.decoder
  rw [← evalDecoder, fields_value binding native.2]
  exact mem

end Airbender.UnifiedReduced.Proth120
