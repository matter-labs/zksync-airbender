import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Tables.BlockSlices

namespace Airbender.Setup.Proofs
open Lean Elab Command

private theorem split_left (whole left middle outside : Array Block)
    (equal : whole = Array.append left middle) :
    Array.append whole outside = Array.append left (Array.append middle outside) := by
  subst whole
  exact @Array.append_assoc Block left middle outside
private theorem split_right (outside whole middle right : Array Block)
    (equal : whole = Array.append middle right) :
    Array.append outside whole = Array.append (Array.append outside middle) right := by
  subst whole
  exact (@Array.append_assoc Block outside middle right).symm
private theorem split_empty (whole : Array Block) : whole = Array.append #[] whole := by simp
private theorem split_full (whole : Array Block) : whole = Array.append whole #[] := by simp

/-- Reuse an equality of imported prefix arrays without reducing their cells. -/
theorem getFromBlocks_common_eq (frontA frontB : Array Block) (left right : List Block)
    (frontEqual : frontA = frontB)
    (tailEqual : ∀ n, getFromBlocks left n = getFromBlocks right n) (n : Nat) :
    getFromBlocks (frontA.toList ++ left) n = getFromBlocks (frontB.toList ++ right) n := by
  cases frontEqual
  exact getFromBlocks_common _ _ _ tailEqual n

/-- One compositional step over a certified imported array split. -/
theorem split_blocks_agree (wholeA wholeB frontA frontB backA backB : Array Block)
    (splitA : wholeA = Array.append frontA backA)
    (splitB : wholeB = Array.append frontB backB) (frontEqual : frontA = frontB)
    (backEqual : ∀ n, getFromBlocks backA.toList n = getFromBlocks backB.toList n) (n : Nat) :
    getFromBlocks wholeA.toList n = getFromBlocks wholeB.toList n := by
  rw [splitA, splitB, raw_toList_append, raw_toList_append]
  exact getFromBlocks_common_eq _ _ _ _ frontEqual backEqual n

/-- Column-shaped wrapper keeps the original imported data opaque during
    composition; the generic proof unfolds only a variable Column. -/
theorem column_split_blocks_agree (wholeA wholeB : Column) (frontA frontB backA backB : Array Block)
    (splitA : wholeA.blocks = Array.append frontA backA)
    (splitB : wholeB.blocks = Array.append frontB backB) (frontEqual : frontA = frontB)
    (backEqual : ∀ n, getFromBlocks backA.toList n = getFromBlocks backB.toList n) (n : Nat) :
    wholeA.get? n = wholeB.get? n := by
  exact split_blocks_agree wholeA.blocks wholeB.blocks frontA frontB backA backB
    splitA splitB frontEqual backEqual n

private theorem normalized_pair (whole left right newLeft newRight : Array Block)
    (split : whole = Array.append left right) (leftEqual : left = newLeft)
    (rightEqual : right = newRight) : whole = Array.append newLeft newRight := by
  cases leftEqual
  cases rightEqual
  exact split

private def blocksType : Lean.Expr :=
  mkApp (mkConst ``Array [Level.zero]) (mkConst ``Block)
private def appendExpr (left right : Lean.Expr) : Lean.Expr :=
  mkApp3 (mkConst ``Array.append [Level.zero]) (mkConst ``Block) left right
private def reflExpr (value : Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) blocksType value

private partial def splitExpr (value : Lean.Expr) (cut : Nat) :
    CommandElabM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let totalBlocks := (← literalArray value).size
  let empty := balancedArray #[]
  if cut = 0 then return (empty, value, mkApp (mkConst ``split_empty) value)
  if cut = totalBlocks then return (value, empty, mkApp (mkConst ``split_full) value)
  unless cut < totalBlocks do throwError "block split is outside imported array"
  if value.getAppFn.isConstOf ``Array.append then
    let args := value.getAppArgs
    let left := args[1]!
    let right := args[2]!
    let leftCount := (← literalArray left).size
    if cut = leftCount then return (left, right, reflExpr value)
    if cut < leftCount then
      let (front, middle, proof) ← splitExpr left cut
      return (front, appendExpr middle right,
        mkAppN (mkConst ``split_left) #[left, front, middle, right, proof])
    else
      let (middle, back, proof) ← splitExpr right (cut - leftCount)
      return (appendExpr left middle, back,
        mkAppN (mkConst ``split_right) #[left, right, middle, back, proof])
  let values ← literalArray value
  return (balancedArray (values.extract 0 cut), balancedArray (values.extract cut totalBlocks), reflExpr value)

/-- Rebalance a stored block array with local congruence certificates. Each
    definitional leaf check is bounded to 64 existing block expressions. -/
private partial def normalizeExpr (value : Lean.Expr) : CommandElabM (Lean.Expr × Lean.Expr) := do
  let values ← literalArray value
  if values.size ≤ 64 then return (balancedArray values, reflExpr value)
  let (left, right, split) ← splitExpr value (values.size / 2)
  let (newLeft, leftProof) ← normalizeExpr left
  let (newRight, rightProof) ← normalizeExpr right
  return (appendExpr newLeft newRight, mkAppN (mkConst ``normalized_pair)
    #[value, left, right, newLeft, newRight, split, leftProof, rightProof])

/-- Split a real imported block tree and emit a kernel-checked reconstruction
    theorem by local append congruence. Leaf reductions inspect at most 64 blocks. -/
elab "split_imported_blocks " left:ident right:ident proof:ident
    " from " source:ident " at " cut:num : command => do
  let sourceName ← resolveGlobalConstNoOverload source
  let info ← getConstInfoDefn sourceName
  let (value, original) ← if info.type.isConstOf ``Column then do
    unless info.value.getAppFn.isConstOf ``Column.mk do throwError "expected imported Column"
    pure (info.value.getAppArgs[0]!, mkApp (mkConst ``Column.blocks) (mkConst sourceName))
  else do
    unless info.type.getAppFn.isConstOf ``Array do throwError "expected imported block array"
    pure (info.value, mkConst sourceName)
  let (originalFront, back, split) ← splitExpr value cut.getNat
  let (front, frontProof) ← normalizeExpr originalFront
  let certificate := mkAppN (mkConst ``normalized_pair)
    #[value, originalFront, back, front, back, split, frontProof, reflExpr back]
  let ns ← getCurrNamespace
  let leftName := ns ++ left.getId
  let rightName := ns ++ right.getId
  for (name, data) in #[(leftName, front), (rightName, back)] do
    liftCoreM <| addDecl (.defnDecl {
      name, levelParams := [], type := blocksType, value := data,
      hints := .regular (getMaxHeight (← getEnv) data + 1), safety := .safe })
    modifyEnv (addNoncomputable · name)
  let type := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) blocksType original
    (appendExpr (mkConst leftName) (mkConst rightName))
  liftCoreM <| addDecl (.thmDecl {
    name := ns ++ proof.getId, levelParams := [], type, value := certificate })

end Airbender.Setup.Proofs
