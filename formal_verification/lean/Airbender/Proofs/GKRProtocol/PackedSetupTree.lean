import Airbender.Proofs.GKRProtocol.PackedSetupEquality

namespace Airbender.Compiler.PackedSetupEquality
set_option warningAsError true

/-- Leaves contain bounded data. Branch sizes are checked by `valid`. -/
inductive CodeTree where
  | leaf (blocks : List BlockCode)
  | branch (leftSize : Nat) (left right : CodeTree)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

def CodeTree.blocks : CodeTree → List BlockCode
  | .leaf blocks => blocks
  | .branch _ left right => left.blocks ++ right.blocks

def CodeTree.size : CodeTree → Nat
  | .leaf blocks => blocks.length
  | .branch leftSize _ right => leftSize + right.size

def CodeTree.valid : CodeTree → Bool
  | .leaf _ => true
  | .branch leftSize left right =>
      (leftSize == left.size) && left.valid && right.valid

theorem CodeTree.size_sound (tree : CodeTree) (checked : tree.valid = true) :
    tree.size = tree.blocks.length := by
  induction tree with
  | leaf blocks => rfl
  | branch size left right first second =>
      simp only [valid, Bool.and_eq_true, beq_iff_eq] at checked
      simp only [CodeTree.size, blocks, List.length_append]
      rw [checked.1.1, first checked.1.2, second checked.2]

private theorem rowCount_append (left right : List BlockCode) (first count : Nat) :
    rowCount (left ++ right) first count =
      rowCount left first count +
        rowCount right (first - left.length) (count - (left.length - first)) := by
  simp only [rowCount, List.drop_append, List.take_append, List.length_drop,
    List.map_append, List.sum_append]

/-- Select whole branches by numeric block counts. Do not flatten the tree. -/
def CodeTree.rowCount : CodeTree → Nat → Nat → Nat
  | .leaf blocks, first, count => PackedSetupEquality.rowCount blocks first count
  | .branch size left right, first, count =>
      if count = 0 then 0
      else if size ≤ first then right.rowCount (first - size) count
      else left.rowCount first count + right.rowCount 0 (count - (size - first))

theorem CodeTree.rowCount_sound (tree : CodeTree) (checked : tree.valid = true)
    (first count : Nat) :
    tree.rowCount first count = PackedSetupEquality.rowCount tree.blocks first count := by
  induction tree generalizing first count with
  | leaf blocks => rfl
  | branch size left right firstIH secondIH =>
      simp only [valid, Bool.and_eq_true, beq_iff_eq] at checked
      have size_eq : size = left.blocks.length := checked.1.1.trans (left.size_sound checked.1.2)
      simp only [CodeTree.rowCount, blocks]
      split
      · next zero => subst count; simp [PackedSetupEquality.rowCount]
      · split
        · next beyond =>
            rw [secondIH checked.2]
            have empty : left.blocks.drop first = [] := List.drop_eq_nil_iff.mpr (by omega)
            rw [rowCount_append]
            simp only [PackedSetupEquality.rowCount, empty, List.take_nil, List.map_nil, List.sum_nil, Nat.zero_add]
            have sub : left.blocks.length - first = 0 := by omega
            rw [sub, Nat.sub_zero, size_eq]
        · next inside =>
            rw [firstIH checked.1.2, secondIH checked.2, rowCount_append, ← size_eq]
            have sub : first - size = 0 := by omega
            rw [sub]

/-- Return the leaf that contains the selected block position. -/
def CodeTree.chunk : CodeTree → Nat → List BlockCode
  | .leaf blocks, _ => blocks
  | .branch size left right, first =>
      if first < size then left.chunk first else right.chunk (first - size)

theorem decoded_row_sum (blocks : List BlockCode) :
    ((blocks.map BlockCode.decode).map Airbender.Setup.Block.length).sum =
      rowCount blocks 0 blocks.length := by
  simp only [rowCount, List.drop_zero, List.take_length, List.map_map,
    Function.comp_def, BlockCode.decode_length]

def checkTree (left right : CodeTree) (lengths : List LengthCheck) : Bool :=
  left.valid && (left == right) &&
    lengths.all (fun item => left.rowCount item.first item.count == item.expected)

theorem checkTree_codes_eq (left right : CodeTree) (lengths : List LengthCheck)
    (checked : checkTree left right lengths = true) : left = right := by
  simp only [checkTree, Bool.and_eq_true, beq_iff_eq] at checked
  exact checked.1.2

theorem checkTree_rows (left right : CodeTree) (lengths : List LengthCheck)
    (checked : checkTree left right lengths = true) (index : Fin lengths.length) :
    left.rowCount lengths[index.val].first lengths[index.val].count = lengths[index.val].expected := by
  simp only [checkTree, Bool.and_eq_true] at checked
  have accepted := List.all_eq_true.mp checked.2 _ (List.getElem_mem index.isLt)
  simpa only [beq_iff_eq] using accepted

theorem checkTree_sound (left right : CodeTree) (lengths : List LengthCheck)
    (checked : checkTree left right lengths = true) :
    left.blocks.map BlockCode.decode = right.blocks.map BlockCode.decode ∧
    ∀ item ∈ lengths,
      ((((left.blocks.map BlockCode.decode).drop item.first).take item.count).map Airbender.Setup.Block.length).sum = item.expected := by
  simp only [checkTree, Bool.and_eq_true, beq_iff_eq] at checked
  refine ⟨congrArg (fun tree : CodeTree => tree.blocks.map BlockCode.decode) checked.1.2, ?_⟩
  intro item member
  have accepted := List.all_eq_true.mp checked.2 item member
  have rows : left.rowCount item.first item.count = item.expected := by
    simpa only [beq_iff_eq] using accepted
  exact (rowCount_eq _ _ _).symm.trans ((left.rowCount_sound checked.1.1 _ _).symm.trans rows)

/-- Check the complete family and the whole-leaf lengths used by projections. -/
def checkTreeWithChunks (left right : CodeTree) (lengths : List LengthCheck) : Bool :=
  checkTree left right lengths && lengths.all (fun item =>
    rowCount (left.chunk item.first) 0 (left.chunk item.first).length == item.expected)

theorem checkTreeWithChunks_base (left right : CodeTree) (lengths : List LengthCheck)
    (checked : checkTreeWithChunks left right lengths = true) :
    checkTree left right lengths = true := by
  simp only [checkTreeWithChunks, Bool.and_eq_true] at checked
  exact checked.1

theorem checkTreeWithChunks_chunk_length (left right : CodeTree) (lengths : List LengthCheck)
    (checked : checkTreeWithChunks left right lengths = true) (index : Fin lengths.length) :
    (((left.chunk lengths[index.val].first).map BlockCode.decode).map Airbender.Setup.Block.length).sum =
      lengths[index.val].expected := by
  simp only [checkTreeWithChunks, Bool.and_eq_true] at checked
  have accepted := List.all_eq_true.mp checked.2 _ (List.getElem_mem index.isLt)
  exact (decoded_row_sum _).trans (by simpa only [beq_iff_eq] using accepted)

theorem checkTreeWithChunks_sound (left right : CodeTree) (lengths : List LengthCheck)
    (checked : checkTreeWithChunks left right lengths = true) :
    (left.blocks.map BlockCode.decode = right.blocks.map BlockCode.decode ∧
      ∀ item ∈ lengths,
        ((((left.blocks.map BlockCode.decode).drop item.first).take item.count).map Airbender.Setup.Block.length).sum = item.expected) ∧
    ∀ index : Fin lengths.length,
      (((left.chunk lengths[index.val].first).map BlockCode.decode).map Airbender.Setup.Block.length).sum = lengths[index.val].expected :=
  ⟨checkTree_sound _ _ _ (checkTreeWithChunks_base _ _ _ checked),
    checkTreeWithChunks_chunk_length _ _ _ checked⟩

/-- Reassemble two data views without unfolding their numeric records. -/
theorem take_drop_append (values : List BlockCode) (count : Nat) (rest : List BlockCode) :
    values.take count ++ (values.drop count ++ rest) = values ++ rest := by
  rw [← List.append_assoc, List.take_append_drop]

end Airbender.Compiler.PackedSetupEquality
