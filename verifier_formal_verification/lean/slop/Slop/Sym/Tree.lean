import Slop.Sym.Check

/-! # Reading values back: a node as an expression tree

`toTree p cut d i` unfolds node `i` to depth `d`, stopping at the ids in `cut` (and at depth 0) with a reference
`.ref j`, which means `p.val c j`. Its evaluation is the node's value (`toTree_eval`), so a proof can replace an id by
the term it denotes, cut at chosen intermediate values. -/

namespace RV.Sym

variable (c : Ctx)

deriving instance DecidableEq for RV.Op
deriving instance DecidableEq for RV.FieldOp

inductive Tree
  | ref (i : Nat)
  | var (i : Nat)
  | const (w : Word)
  | op (o : Op) (a b : Tree)
  | mop (o : FieldOp) (a b x : Tree)
  | load (n : Nat) (sg : Bool) (b : Tree) (off : Word)
deriving DecidableEq

def Tree.eval (g : Nat → Word) : Tree → Word
  | .ref i => g i
  | .var i => c.env i
  | .const w => w
  | .op o a b => alu o (a.eval g) (b.eval g)
  | .mop o a b x => mopVal o (a.eval g) (b.eval g) (x.eval g)
  | .load n sg b off => if sg then ((read c.m (b.eval g + off) n).setWidth (8 * n)).signExtend 32
      else read c.m (b.eval g + off) n

/-- The node with id `i`. -/
def nodeAt (p : Pool) (i : Nat) : Node := p.nodes.getD (p.len - 1 - i) (.const 0)

def toTree (p : Pool) (cut : List Nat) : Nat → Nat → Tree
  | 0, i => .ref i
  | d + 1, i => if cut.contains i then .ref i else
    match nodeAt p i with
    | .var j => .var j
    | .const w => .const w
    | .op o a b => .op o (toTree p cut d a) (toTree p cut d b)
    | .mop o a b x => .mop o (toTree p cut d a) (toTree p cut d b) (toTree p cut d x)
    | .load n sg b off => .load n sg (toTree p cut d b) off

theorem nodeAt_spec (p : Pool) (hw : p.WF) (i : Nat) (hi : i < p.len) :
    (nodeAt p i).childLt i = true ∧ p.val c i = (nodeAt p i).eval c (p.val c) := by
  obtain ⟨hn, -, hl⟩ := hw
  have hd : p.len - 1 - i < p.nodes.length := by omega
  have hget : nodeAt p i = p.nodes[p.len - 1 - i] := by
    simp only [nodeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd, Option.getD_some]
  have e : p.nodes.length - 1 - (p.len - 1 - i) = i := by omega
  refine ⟨?_, ?_⟩
  · have := wf_get p.nodes hn _ hd; rw [e] at this; rw [hget]; exact this
  · have := val_at c p.nodes hn _ hd; rw [e] at this
    rw [hget]; exact this

theorem toTree_eval (p : Pool) (hw : p.WF) (cut : List Nat) :
    ∀ d i, i < p.len → (toTree p cut d i).eval c (p.val c) = p.val c i
  | 0, i, _ => rfl
  | d + 1, i, hi => by
    obtain ⟨hlt, hv⟩ := nodeAt_spec c p hw i hi
    simp only [toTree]
    split
    · rfl
    · rw [hv]
      generalize nodeAt p i = n at hlt
      cases n <;> simp only [Node.childLt, Bool.and_eq_true, decide_eq_true_eq] at hlt <;>
        simp only [Tree.eval, Node.eval]
      · rw [toTree_eval p hw cut d _ (by omega), toTree_eval p hw cut d _ (by omega)]
      · rw [toTree_eval p hw cut d _ (by omega), toTree_eval p hw cut d _ (by omega),
          toTree_eval p hw cut d _ (by omega)]
      · rw [toTree_eval p hw cut d _ (by omega)]

/-- The value of the 4 bytes at `val b + k` after the block, if the last write there stored them: its node id. -/
def outNode (σ : SState) (b : Nat) (k : Word) : Nat :=
  match resolve b k 4 σ.writes [] with
  | some (some x, _) => x.val
  | _ => 0

/-- `outNode` is right, and its side conditions pass the checker. -/
def outOK (σ : SState) (rs : List Region) (aps : List (Region × Region)) (b : Nat) (k : Word) : Bool :=
  decide (b < σ.pool.len) &&
  match resolve b k 4 σ.writes [] with
  | some (some _, cs) => cs.all (checkCond rs aps)
  | _ => false

theorem read_out (σ : SState) (S : State) (hrel : Rel c σ S) (rs : List Region) (aps : List (Region × Region))
    (hR : ∀ R ∈ rs, R.Holds c σ.pool)
    (hA : ∀ q ∈ aps, q.1 ∈ rs → q.2 ∈ rs → Apart c σ.pool q.1 q.2)
    (b : Nat) (k : Word) (h : outOK σ rs aps b k = true) :
    read S.mem (σ.pool.val c b + k) 4 = σ.pool.val c (outNode σ b k) := by
  simp only [outOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hb, h⟩ := h
  simp only [outNode]
  split at h
  · rename_i x cs hres
    obtain ⟨-, -, -, h4⟩ := resolve_spec c σ b k 4 σ.writes [] cs (some x) hres hrel.2.2.2.1 hb
    have hh : ∀ y ∈ cs, y.Holds c σ := fun y hy => checkCond_sound c σ rs aps hR hA y (List.all_eq_true.mp h y hy)
    obtain ⟨-, -, h4⟩ := h4 hh
    rw [hrel.2.2.2.2]; exact h4
  · cases h

end RV.Sym
