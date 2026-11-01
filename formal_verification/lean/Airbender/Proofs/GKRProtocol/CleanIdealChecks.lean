import Airbender.Proofs.GKRProtocol.CleanArithmetic
import Airbender.Proofs.GKRProtocol.NumericExpressionChecks
import Airbender.Proofs.GKRProtocol.NumericArithmeticChecks

namespace Airbender.Compiler.CleanIdealChecks
open NumericPolynomialChecks
set_option warningAsError true

/-- Erase the original Clean AST before expanding its polynomial. -/
def encode (placement : Nat → Fin n) : _root_.Expression (ZMod p) → NumericExpressionChecks.Code
  | .var wire => .atom (placement wire.index).val
  | .const value => .constant value.val
  | .add left right => .add (encode placement left) (encode placement right)
  | .mul left right => .mul (encode placement left) (encode placement right)

theorem encode_polynomial (placement : Nat → Fin n) (expression : _root_.Expression (ZMod p)) :
    NumericPolynomialChecks.encode (CleanExpression.polynomial placement expression) =
      NumericExpressionChecks.Code.polynomial p (encode placement expression) := by
  induction expression with
  | var wire => exact NumericPolynomialChecks.encode_atom _
  | const value => rfl
  | add left right ihLeft ihRight =>
    simp only [CleanExpression.polynomial, encode, NumericExpressionChecks.Code.polynomial,
      Compiler.add, NumericPolynomialChecks.encode_append, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
    simp only [CleanExpression.polynomial, encode, NumericExpressionChecks.Code.polynomial,
      NumericPolynomialChecks.encode_multiply, ihLeft, ihRight]

def mapTable (function : α → β) : LookupTable α → LookupTable β
  | .leaf items => .leaf (items.map function)
  | .branch size left right => .branch size (mapTable function left) (mapTable function right)

theorem mapTable_size (function : α → β) (data : LookupTable α) :
    (mapTable function data).size = data.size := by
  induction data with
  | leaf items => simp only [mapTable, LookupTable.size, List.length_map]
  | branch size left right leftIH rightIH => simp only [mapTable, LookupTable.size, rightIH]

theorem mapTable_valid (function : α → β) (data : LookupTable α) :
    (mapTable function data).valid = data.valid := by
  induction data with
  | leaf items => rfl
  | branch size left right leftIH rightIH =>
    simp only [mapTable, LookupTable.valid, mapTable_size, leftIH, rightIH]

theorem mapTable_toList (function : α → β) (data : LookupTable α) :
    (mapTable function data).toList = data.toList.map function := by
  induction data with
  | leaf items => rfl
  | branch size left right leftIH rightIH =>
    simp only [mapTable, LookupTable.toList, List.map_append, leftIH, rightIH]

theorem mapTable_getD (function : α → β) (data : LookupTable α) (index : Nat) (fallback : α) :
    (mapTable function data).getD index (function fallback) = function (data.getD index fallback) := by
  induction data generalizing index with
  | leaf items =>
    simp only [mapTable, LookupTable.getD, List.getElem?_map]
    cases items[index]? <;> rfl
  | branch size left right leftIH rightIH =>
    simp only [mapTable, LookupTable.getD]
    split
    · exact leftIH index
    · exact rightIH (index - size)

structure Capture where
  codes : LookupTable NumericExpressionChecks.Code
  relations : LookupTable Data
  witnesses : LookupTable (List (Data × Nat))
  inputs : LookupTable (List Nat)
  scopeLimit : Nat

def layoutCheck (data : Capture) : Bool :=
  data.codes.valid && data.relations.valid && data.witnesses.valid && data.inputs.valid &&
    data.witnesses.size == data.codes.size && data.inputs.size == data.codes.size

def idealCheck (p : Nat) (data : Capture) : Bool :=
  (List.range data.codes.size).all fun index => NumericPolynomialChecks.fastEqual p
    (NumericExpressionChecks.Code.polynomial p (data.codes.getD index (.constant 0)))
    (NumericArithmeticChecks.combine p data.relations (data.witnesses.getD index []))

def scopeCheck (data : Capture) : Bool :=
  (List.range data.inputs.size).all fun index =>
    (data.inputs.getD index []).all fun wire => decide (wire < data.scopeLimit)

def check (p : Nat) (data : Capture) : Bool := layoutCheck data && idealCheck p data && scopeCheck data

structure Layout (data : Capture) : Prop where
  codes : data.codes.valid = true
  relations : data.relations.valid = true
  witnesses : data.witnesses.valid = true
  inputs : data.inputs.valid = true
  witnessSize : data.witnesses.size = data.codes.size
  inputSize : data.inputs.size = data.codes.size

theorem layout_sound (data : Capture) (checked : layoutCheck data = true) : Layout data := by
  simp only [layoutCheck, Bool.and_eq_true, beq_iff_eq] at checked
  rcases checked with ⟨⟨⟨⟨⟨codes, relations⟩, witnesses⟩, inputs⟩, witnessSize⟩, inputSize⟩
  exact ⟨codes, relations, witnesses, inputs, witnessSize, inputSize⟩

structure Bindings (placement : Nat → Fin n) (relations : List (Polynomial n (ZMod p)))
    (expressions : LookupTable (_root_.Expression (ZMod p)))
    (witnesses : LookupTable (Combination relations)) (data : Capture) : Prop where
  codes : mapTable (encode placement) expressions = data.codes
  relations : relations.map NumericPolynomialChecks.encode = data.relations.toList
  witnesses : mapTable NumericPolynomialChecks.encodeCombination witnesses = data.witnesses
  inputs : mapTable CleanExpression.inputs expressions = data.inputs

/-- Derive an original named fact from its exact numeric source bindings. -/
theorem check_sound_at [NeZero p] (placement : Nat → Fin n)
    (relations : List (Polynomial n (ZMod p))) (expression : _root_.Expression (ZMod p))
    (witness : Combination relations) (data : Capture) (checked : check p data = true)
    (index : Nat) (inside : index < data.codes.size)
    (expressionBinding : encode placement expression = data.codes.getD index (.constant 0))
    (relationsBinding : relations.map NumericPolynomialChecks.encode = data.relations.toList)
    (witnessBinding : NumericPolynomialChecks.encodeCombination witness = data.witnesses.getD index []) :
    Airbender.Compiler.equal (CleanExpression.polynomial placement expression)
      (Airbender.Compiler.combination relations witness) = true := by
  simp only [check, Bool.and_eq_true] at checked
  have layout := layout_sound data checked.1.1
  have row := List.all_eq_true.mp checked.1.2 index (List.mem_range.mpr inside)
  have left : NumericExpressionChecks.Code.polynomial p (data.codes.getD index (.constant 0)) =
      NumericPolynomialChecks.encode (CleanExpression.polynomial placement expression) := by
    rw [← expressionBinding, encode_polynomial]
  have right : NumericArithmeticChecks.combine p data.relations (data.witnesses.getD index []) =
      NumericPolynomialChecks.encode (Airbender.Compiler.combination relations witness) := by
    rw [NumericArithmeticChecks.combine_eq p _ layout.relations, ← witnessBinding,
      ← relationsBinding, ← NumericPolynomialChecks.encode_combination]
  rw [NumericPolynomialChecks.fastEqual_eq, left, right, NumericPolynomialChecks.equal_encode] at row
  exact row

theorem scope_at {F : Type} (expression : _root_.Expression F) (data : Capture)
    (checked : check p data = true) (index : Nat) (inside : index < data.inputs.size)
    (binding : CleanExpression.inputs expression = data.inputs.getD index []) :
    (CleanExpression.inputs expression).all (fun wire => decide (wire < data.scopeLimit)) = true := by
  simp only [check, Bool.and_eq_true] at checked
  have row := List.all_eq_true.mp checked.2 index (List.mem_range.mpr inside)
  rwa [← binding] at row

theorem check_sound [NeZero p] (placement : Nat → Fin n)
    (relations : List (Polynomial n (ZMod p)))
    (expressions : LookupTable (_root_.Expression (ZMod p)))
    (witnesses : LookupTable (Combination relations)) (data : Capture)
    (binding : Bindings placement relations expressions witnesses data)
    (checked : check p data = true) (index : Nat) (inside : index < expressions.size) :
    equal (CleanExpression.polynomial placement (expressions.getD index (.const 0)))
      (combination relations (witnesses.getD index [])) = true := by
  simp only [check, Bool.and_eq_true] at checked
  have layout := layout_sound data checked.1.1
  have codeSize : data.codes.size = expressions.size := by rw [← binding.codes, mapTable_size]
  have row := List.all_eq_true.mp checked.1.2 index (List.mem_range.mpr (by omega))
  have source : data.codes.getD index (.constant 0) = encode placement (expressions.getD index (.const 0)) := by
    rw [← binding.codes]
    simpa only [encode, ZMod.val_zero] using mapTable_getD (encode placement) expressions index (.const 0)
  have left : NumericExpressionChecks.Code.polynomial p (data.codes.getD index (.constant 0)) =
      NumericPolynomialChecks.encode (CleanExpression.polynomial placement (expressions.getD index (.const 0))) := by
    rw [source, encode_polynomial]
  have certificate : data.witnesses.getD index [] =
      NumericPolynomialChecks.encodeCombination (witnesses.getD index []) := by
    rw [← binding.witnesses]
    exact mapTable_getD NumericPolynomialChecks.encodeCombination witnesses index []
  have right : NumericArithmeticChecks.combine p data.relations (data.witnesses.getD index []) =
      NumericPolynomialChecks.encode (combination relations (witnesses.getD index [])) := by
    rw [NumericArithmeticChecks.combine_eq p _ layout.relations, certificate,
      ← binding.relations, ← NumericPolynomialChecks.encode_combination]
  rw [NumericPolynomialChecks.fastEqual_eq, left, right, NumericPolynomialChecks.equal_encode] at row
  exact row

theorem scope_sound (placement : Nat → Fin n)
    (relations : List (Polynomial n (ZMod p)))
    (expressions : LookupTable (_root_.Expression (ZMod p)))
    (witnesses : LookupTable (Combination relations)) (data : Capture)
    (binding : Bindings placement relations expressions witnesses data)
    (checked : check p data = true) :
    expressions.toList.all (fun expression => (CleanExpression.inputs expression).all
      (fun wire => decide (wire < data.scopeLimit))) = true := by
  simp only [check, Bool.and_eq_true] at checked
  have layout := layout_sound data checked.1.1
  have whole : data.inputs.toList.all (fun inputs => inputs.all (fun wire => decide (wire < data.scopeLimit))) = true := by
    apply List.all_eq_true.mpr
    intro inputs member
    obtain ⟨index, same⟩ := List.mem_iff_get.mp member
    have inside : index.val < data.inputs.size := by
      rw [LookupTable.size_eq_length _ layout.inputs]
      exact index.isLt
    have result := List.all_eq_true.mp checked.2 index.val (List.mem_range.mpr inside)
    rw [LookupTable.getD_eq _ layout.inputs, List.getElem?_eq_getElem index.isLt,
      Option.getD_some, ← List.get_eq_getElem, same] at result
    exact result
  rw [← binding.inputs, mapTable_toList, List.all_map] at whole
  exact whole

end Airbender.Compiler.CleanIdealChecks
