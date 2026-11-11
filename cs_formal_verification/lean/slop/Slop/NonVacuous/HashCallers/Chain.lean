module
public import Slop.NonVacuous.Blake2GSpan.From
public import Slop.Constraints
public import Human.Helpers.Delegation.Requests

@[expose] public section

/-! A chain of delegation caller rows over the shared memory: each caller reads x0 at its clock `c` (last written at
    its `previous` clock) and writes it at `c` and `c + 2`; the next caller's previous clock is `c + 2`. The x0 tokens
    of the chain are the edges of a sequential run that touches only x0 (`x0_run`), and the rows' PC/clock states
    chain from the first row's start to the last row's finish (`chain_perm`). -/

namespace Airbender.NonVacuous.HashCallers
open Trace NonVacuous.Blake2GSpan

local notation "P" => babyBearModulus

/-- The x0 token last written at clock `t` (x0 holds zero). -/
def x0Token (t : Nat) : MemoryToken P := ⟨(Cell.register 0).addressCode, ((t : ZMod P), ((0 : Nat) : ZMod P)), Nat.pair 0 0⟩

/-- One caller's x0 steps: the source port's write at `c`, the destination port's write at `c + 2`. -/
def x0Steps (c : Nat) : List (Cell × MemoryToken P) := [(.register 0, x0Token c), (.register 0, x0Token (c + 2))]

/-- One caller's x0 edges: read the token of `previous`, then the source port's write. -/
def x0Edges (previous c : Nat) : List (MemoryToken P × MemoryToken P) :=
  [(x0Token previous, x0Token c), (x0Token c, x0Token (c + 2))]

/-- The x0 chain of `n` callers is a run from any memory holding x0's token of the first previous clock; it touches
    only x0. -/
theorem x0_run {base : Memory} {clock previous : Nat → Nat} (n : Nat)
    (first : base (.register 0) = x0Token (previous 0)) (chain : ∀ k < n, previous (k + 1) = clock k + 2) :
    (List.range n).flatMap (fun k => x0Edges (previous k) (clock k)) =
        runEdges base ((List.range n).flatMap fun k => x0Steps (clock k)) ∧
      ∀ cell, cell ≠ .register 0 → runFinal base ((List.range n).flatMap fun k => x0Steps (clock k)) cell = base cell := by
  have start : Function.update base (.register 0) (x0Token (previous 0)) = base := by
    rw [← first]
    exact Function.update_eq_self _ _
  obtain ⟨edges, final⟩ := run_blocks (mem := fun k => Function.update base (.register 0) (x0Token (previous k)))
    (steps := fun k => x0Steps (clock k)) (edges := fun k => x0Edges (previous k) (clock k)) n
    (fun k small => by simp only [x0Steps, runFinal, Function.update_idem, chain k small])
    (fun k _ => by simp only [x0Edges, x0Steps, runEdges, Function.update_self])
  simp only [start] at edges final
  refine ⟨edges, fun cell other => ?_⟩
  rw [final, Function.update_of_ne other]

/-- Rows whose finishes are the next rows' starts: the first start and the finishes are a permutation of the last
    finish and the starts. -/
theorem chain_perm {α : Type} {start finish : Nat → α} (n : Nat) (chain : ∀ k < n, finish k = start (k + 1)) :
    (start 0 :: (List.range (n + 1)).map finish).Perm (finish n :: (List.range (n + 1)).map start) := by
  have shape : start 0 :: (List.range (n + 1)).map finish = (List.range (n + 1)).map start ++ [finish n] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ (n := n + 1), List.map_append, ← List.cons_append, ih (fun k small => chain k (by omega)),
        List.map_append, chain n (by omega)]
      simp
  rw [shape]
  exact List.perm_append_comm

/-- A range query whose entry evaluates to a natural number below `2^16`. -/
theorem range16_of_eval {e : Expression (ZMod P)} {env : Environment (ZMod P)} {n : Nat}
    (value : e.eval env = (n : ZMod P)) (bound : n < 65536) : (Verification.range16 e).Contains env :=
  Verification.range16_contains (by
    rw [value, ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega)]
    exact bound)

/-- The clock at which caller `k`'s source port finds x0 last written. -/
def previousOf (p0 c0 k : Nat) : Nat := if k = 0 then p0 else c0 + 4 * k - 2

theorem previous_chain {p0 c0 n : Nat} : ∀ k < n, previousOf p0 c0 (k + 1) = c0 + 4 * k + 2 := by
  intro k _
  rw [previousOf, ite_eq_right (Nat.succ_ne_zero k)]
  omega

/-- The G request of caller `k`. -/
def requestAt (c0 k : Nat) : Delegation.Requests.Request P :=
  ⟨Delegation.Requests.csr .blakeG, (((c0 + 1 + 4 * k : Nat) : ZMod P), ((0 : Nat) : ZMod P))⟩

/-- The span from `c0 + 1` fulfills exactly the block's requests, in order. -/
theorem fulfillments {c0 : Nat} (m0 : Memory) : (workersFrom m0 (c0 + 1)).rows.map Delegation.Requests.fulfillment =
    (List.range 56).map (requestAt c0) := by
  simp only [workersFrom, rowsFrom, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, Delegation.Requests.fulfillment, requestAt]
  rw [invocation_raw]
  rfl

end Airbender.NonVacuous.HashCallers
