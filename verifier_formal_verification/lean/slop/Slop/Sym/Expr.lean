import Human.RV32
import Mathlib.Data.Nat.Pairing

/-! # Symbolic words, hash-consed

A symbolic value is a node id into a list of `Node`s whose children are earlier ids. The list is kept newest first
(cons is O(1) for the kernel) together with injective `Nat` keys, so hash-consing is a scan comparing `Nat`s.
Everything here is evaluated by the kernel (`decide +kernel`): plain structural recursion, `Nat` arithmetic. -/

namespace RV.Sym

/-- A symbolic 32-bit word. Children are ids of earlier nodes. `load n sg b off` reads the *initial* memory at
`val b + off` (as the `load` instruction does). -/
inductive Node
  | var (i : Nat)
  | const (w : Word)
  | op (o : Op) (a b : Nat)
  | mop (o : FieldOp) (a b c : Nat)
  | load (n : Nat) (sg : Bool) (b : Nat) (off : Word)

def opIdx : Op → Nat
  | .add => 0 | .sub => 1 | .sll => 2 | .slt => 3 | .sltu => 4 | .xor => 5 | .srl => 6 | .sra => 7 | .or => 8
  | .and => 9 | .mul => 10 | .mulhu => 11 | .divu => 12 | .remu => 13

def fopIdx : FieldOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .fma => 3 | .triAdd => 4

theorem opIdx_inj {a b : Op} (h : opIdx a = opIdx b) : a = b := by cases a <;> cases b <;> simp_all [opIdx]
theorem fopIdx_inj {a b : FieldOp} (h : fopIdx a = fopIdx b) : a = b := by
  cases a <;> cases b <;> simp_all [fopIdx]

/-- An injective `Nat` code of a node. -/
def Node.key : Node → Nat
  | .var i => Nat.pair 0 i
  | .const w => Nat.pair 1 w.toNat
  | .op o a b => Nat.pair 2 (Nat.pair (opIdx o) (Nat.pair a b))
  | .mop o a b c => Nat.pair 3 (Nat.pair (fopIdx o) (Nat.pair a (Nat.pair b c)))
  | .load n sg b off => Nat.pair 4 (Nat.pair n (Nat.pair (if sg then 1 else 0) (Nat.pair b off.toNat)))

theorem Node.key_inj {x y : Node} (h : x.key = y.key) : x = y := by
  cases x <;> cases y <;> simp only [Node.key, Nat.pair_eq_pair] at h
  all_goals first | (exfalso; omega) | skip
  · rw [h.2]
  · rw [BitVec.toNat_inj.mp h.2]
  · obtain ⟨-, h1, rfl, rfl⟩ := h; rw [opIdx_inj h1]
  · obtain ⟨-, h1, rfl, rfl, rfl⟩ := h; rw [fopIdx_inj h1]
  · obtain ⟨-, rfl, h2, rfl, h4⟩ := h; rw [BitVec.toNat_inj.mp h4]
    congr; revert h2; cases ‹Bool› <;> cases ‹Bool› <;> simp

/-- What the symbolic words mean: the initial registers (`env`) and the initial memory. -/
structure Ctx where
  env : Nat → Word
  m : Word → BitVec 8

/-- Element `i` (oldest first) of a list stored newest first. -/
def getR (vs : List Word) (i : Nat) : Word := vs.getD (vs.length - 1 - i) 0

def Node.eval (c : Ctx) (g : Nat → Word) : Node → Word
  | .var i => c.env i
  | .const w => w
  | .op o a b => alu o (g a) (g b)
  | .mop o a b x => mopVal o (g a) (g b) (g x)
  | .load n sg b off => if sg then ((read c.m (g b + off) n).setWidth (8 * n)).signExtend 32 else read c.m (g b + off) n

/-- All children are below `k`. -/
def Node.childLt (k : Nat) : Node → Bool
  | .var _ => true
  | .const _ => true
  | .op _ a b => a < k && b < k
  | .mop _ a b x => a < k && b < k && x < k
  | .load _ _ b _ => b < k

/-- The values of a node list (newest first). -/
def valsR (c : Ctx) : List Node → List Word
  | [] => []
  | n :: ns => n.eval c (getR (valsR c ns)) :: valsR c ns

/-- A hash-consed node list: nodes newest first, their keys, their number. -/
structure Pool where
  nodes : List Node
  keys : List Nat
  len : Nat

def Pool.val (c : Ctx) (p : Pool) (i : Nat) : Word := getR (valsR c p.nodes) i

/-- Depth (from the newest) of the first occurrence of `k`. -/
def findKey (k : Nat) : List Nat → Option Nat
  | [] => none
  | k' :: ks => if k' = k then some 0 else (findKey k ks).map (· + 1)

/-- The id of `n`: an existing equal node, or a new one (`none` if a child is not in the pool). -/
def Pool.node (p : Pool) (n : Node) : Option (Pool × Nat) :=
  if n.childLt p.len then
    match findKey n.key p.keys with
    | some d => some (p, p.len - 1 - d)
    | none => some (⟨n :: p.nodes, n.key :: p.keys, p.len + 1⟩, p.len)
  else none

/-- Each node's children are earlier nodes; keys and length match. -/
def WFNodes : List Node → Prop
  | [] => True
  | n :: ns => n.childLt ns.length = true ∧ WFNodes ns

def Pool.WF (p : Pool) : Prop := WFNodes p.nodes ∧ p.keys = p.nodes.map Node.key ∧ p.len = p.nodes.length

/-! ## Lemmas -/

theorem valsR_length (c : Ctx) (ns : List Node) : (valsR c ns).length = ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [valsR, ih]

theorem getR_cons (x : Word) (vs : List Word) (i : Nat) (h : i < vs.length) : getR (x :: vs) i = getR vs i := by
  simp only [getR, List.length_cons]
  rw [show vs.length + 1 - 1 - i = (vs.length - 1 - i) + 1 by omega]; rfl

theorem getR_cons_self (x : Word) (vs : List Word) : getR (x :: vs) vs.length = x := by
  simp [getR]

theorem Node.eval_congr (c : Ctx) (n : Node) (k : Nat) (h : n.childLt k = true) (g g' : Nat → Word)
    (hg : ∀ j < k, g j = g' j) : n.eval c g = n.eval c g' := by
  cases n <;> simp only [Node.childLt, Bool.and_eq_true, decide_eq_true_eq] at h <;> simp only [Node.eval]
  · rw [hg _ h.1, hg _ h.2]
  · rw [hg _ h.1.1, hg _ h.1.2, hg _ h.2]
  · rw [hg _ h]

theorem findKey_spec (k : Nat) (ks : List Nat) (d : Nat) (h : findKey k ks = some d) : d < ks.length ∧ ks[d]? = some k := by
  induction ks generalizing d with
  | nil => simp [findKey] at h
  | cons k' ks ih =>
    simp only [findKey] at h
    split at h
    · cases h; simp_all
    · obtain ⟨d', h1, rfl⟩ := Option.map_eq_some_iff.mp h
      have := ih d' h1; simp [this.2]; omega

theorem wf_get (ns : List Node) (hw : WFNodes ns) (d : Nat) (hd : d < ns.length) :
    (ns[d]).childLt (ns.length - 1 - d) = true := by
  induction ns generalizing d with
  | nil => simp at hd
  | cons n ns ih =>
    obtain ⟨hn, hw⟩ := hw
    cases d with
    | zero => simpa using hn
    | succ d =>
      simp only [List.length_cons, List.getElem_cons_succ]
      rw [show ns.length + 1 - 1 - (d + 1) = ns.length - 1 - d by omega]
      exact ih hw d (by simp at hd; omega)

/-- Values of a longer list agree on the older ids. -/
theorem getR_valsR_cons (c : Ctx) (n : Node) (ns : List Node) (i : Nat) (h : i < ns.length) :
    getR (valsR c (n :: ns)) i = getR (valsR c ns) i := by
  simp only [valsR]; exact getR_cons _ _ _ (by rw [valsR_length]; exact h)

/-- The value of the node at depth `d` (id `len - 1 - d`). -/
theorem val_at (c : Ctx) (ns : List Node) (hw : WFNodes ns) (d : Nat) (hd : d < ns.length) :
    getR (valsR c ns) (ns.length - 1 - d) = (ns[d]).eval c (getR (valsR c ns)) := by
  induction ns generalizing d with
  | nil => simp at hd
  | cons n ns ih =>
    have hw' := hw
    obtain ⟨hn, hw⟩ := hw
    cases d with
    | zero =>
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
      have e : getR (valsR c (n :: ns)) ns.length = n.eval c (getR (valsR c ns)) := by
        simp only [valsR]; rw [← valsR_length c ns]; exact getR_cons_self _ _
      rw [e]
      exact Node.eval_congr c n ns.length hn _ _ (fun j hj => (getR_valsR_cons c n ns j hj).symm)
    | succ d =>
      have hd' : d < ns.length := by simp at hd; omega
      simp only [List.length_cons, List.getElem_cons_succ]
      rw [show ns.length + 1 - 1 - (d + 1) = ns.length - 1 - d by omega,
        getR_valsR_cons c n ns _ (by omega), ih hw d hd']
      exact Node.eval_congr c _ _ (wf_get ns hw d hd') _ _ (fun j hj => (getR_valsR_cons c n ns j (by omega)).symm)

/-- What `Pool.node` returns: a well-formed pool extending the old one, and an id whose value is the node's. -/
theorem Pool.node_spec (c : Ctx) (p p' : Pool) (n : Node) (i : Nat) (hw : p.WF) (h : p.node n = some (p', i)) :
    p'.WF ∧ p.len ≤ p'.len ∧ i < p'.len ∧ (∀ j < p.len, p'.val c j = p.val c j) ∧
      p'.val c i = n.eval c (p.val c) := by
  obtain ⟨hwn, hk, hl⟩ := hw
  simp only [Pool.node] at h
  split at h
  · rename_i hch
    split at h
    · rename_i d hd
      cases h
      obtain ⟨hdl, hkd⟩ := findKey_spec _ _ _ hd
      rw [hk, List.length_map] at hdl
      rw [hk, List.getElem?_map, List.getElem?_eq_getElem hdl] at hkd
      have hn : p.nodes[d] = n := Node.key_inj (by simpa using hkd)
      refine ⟨⟨hwn, hk, hl⟩, le_rfl, by omega, fun _ _ => rfl, ?_⟩
      simp only [Pool.val]; rw [hl, val_at c _ hwn d hdl, hn]; rfl
    · cases h
      refine ⟨⟨⟨by rw [← hl]; exact hch, hwn⟩, by simp [hk], by simp [hl]⟩, by simp, by simp, ?_, ?_⟩
      · intro j hj; simp only [Pool.val]; exact getR_valsR_cons c n _ j (by omega)
      · simp only [Pool.val, valsR]; rw [hl, ← valsR_length c p.nodes]; exact getR_cons_self _ _
  · cases h

end RV.Sym