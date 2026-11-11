module
public import Slop.NonVacuous.HashCallers.UnifiedRow
public import Slop.NonVacuous.HashCallers.Span

@[expose] public section

/-! A block of `n` unified caller rows: caller `k` at PC `f + 4 k` and clock `c0 + 4 k`, reading x0 as the previous
    caller left it (the first caller: as written at `p0`). Every fact is one statement over the block, from the
    one-row lemmas of `UnifiedRow.lean`: the rows satisfy the unified constraints, are the selected callers, issue the
    G requests at `c0 + 4 k + 1` (the invocations of the span from `c0 + 1`), decode in the caller table of
    `program f n`, chain their PC/clock states, and their x0 ports are the x0 chain's edges. -/

namespace Airbender.NonVacuous.HashCallers.UnifiedBlock
open Trace NonVacuous.Blake2GSpan

local notation "P" => babyBearModulus

/-- The clock at which caller `k`'s source port finds x0 last written. -/
def previousOf (p0 c0 k : Nat) : Nat := if k = 0 then p0 else c0 + 4 * k - 2

def callerRow (f c0 p0 k : Nat) : Row P UnifiedFamily := UnifiedRow.row (f + 4 * k) (c0 + 4 * k) (previousOf p0 c0 k)

def callerRows (f c0 p0 n : Nat) : List (Row P UnifiedFamily) := (List.range n).map (callerRow f c0 p0)

/-- Room for the block's PCs and clocks; the first caller's x0 was written before its clock. -/
structure Room (f c0 p0 n : Nat) : Prop where
  pc : f + 4 * n < 65536
  clock : c0 + 4 * n < timestampBase
  previous : p0 < c0

variable {f c0 p0 n : Nat}

theorem mem_rows {row : Row P UnifiedFamily} (member : row ∈ callerRows f c0 p0 n) :
    ∃ k < n, row = callerRow f c0 p0 k := by
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  exact ⟨k, List.mem_range.mp present, rfl⟩

theorem valid (room : Room f c0 p0 n) {k : Nat} (small : k < n) :
    UnifiedRow.Valid (f + 4 * k) (c0 + 4 * k) (previousOf p0 c0 k) := by
  have := room.pc
  have := room.clock
  have := room.previous
  refine ⟨by omega, by omega, ?_⟩
  unfold previousOf
  split <;> omega

theorem satisfies (room : Room f c0 p0 n) (before : RV.State) : ∀ row ∈ callerRows f c0 p0 n,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints (UnifiedReduced.Setup.tableRV (p := P) before)) := by
  intro row member
  obtain ⟨k, small, rfl⟩ := mem_rows member
  exact UnifiedRow.satisfies (valid room small) before

theorem active : ∀ row ∈ callerRows f c0 p0 n, row.assignment row.columns.execute = 1 := by
  intro row member
  obtain ⟨k, -, rfl⟩ := mem_rows member
  exact UnifiedRow.active ..

theorem selected : ∀ row ∈ callerRows f c0 p0 n, UnifiedReduced.Caller.Selected row.assignment := by
  intro row member
  obtain ⟨k, -, rfl⟩ := mem_rows member
  exact UnifiedRow.selected ..

/-- Every row of the block is a selected caller. -/
theorem filter_selected :
    (callerRows f c0 p0 n).filter (fun row => decide (UnifiedReduced.Caller.Selected row.assignment)) =
      callerRows f c0 p0 n :=
  List.filter_eq_self.mpr fun row member => decide_eq_true (selected row member)

/-- The G request of caller `k`. -/
def requestAt (c0 k : Nat) : Delegation.Requests.Request P :=
  ⟨Delegation.Requests.csr .blakeG, (((c0 + 1 + 4 * k : Nat) : ZMod P), ((0 : Nat) : ZMod P))⟩

theorem requests : (callerRows f c0 p0 n).map (fun row => UnifiedReduced.Caller.request row.assignment) =
    (List.range n).map (requestAt c0) := by
  rw [callerRows, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, callerRow, UnifiedRow.request, requestAt]
  congr 3
  omega

/-- The span from `c0 + 1` fulfills exactly the block's requests, in order. -/
theorem fulfillments (m0 : Memory) : (workersFrom m0 (c0 + 1)).rows.map Delegation.Requests.fulfillment =
    (List.range 56).map (requestAt c0) := by
  simp only [workersFrom, rowsFrom, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, Delegation.Requests.fulfillment, requestAt]
  rw [invocation_raw]
  rfl

theorem edges : (callerRows f c0 p0 n).flatMap (fun row => (UnifiedReduced.Caller.machinePorts row).toList.map
      (fun port => (readToken row.assignment port, writeToken row.columns row.assignment port))) =
    (List.range n).flatMap (fun k => x0Edges (previousOf p0 c0 k) (c0 + 4 * k)) := by
  rw [callerRows, List.flatMap_map]
  exact List.flatMap_congr fun k _ => UnifiedRow.steps ..

theorem chain : ∀ k < n, previousOf p0 c0 (k + 1) = c0 + 4 * k + 2 := by
  intro k _
  rw [previousOf, ite_eq_right (Nat.succ_ne_zero k)]
  omega

/-- The block's PC/clock states chain from its first start to its last finish. -/
theorem states (m : Nat) :
    ((callerRow f c0 p0 0).start :: (callerRows f c0 p0 (m + 1)).map Row.finish).Perm
      ((callerRow f c0 p0 m).finish :: (callerRows f c0 p0 (m + 1)).map Row.start) := by
  simp only [callerRows, List.map_map]
  exact chain_perm (start := fun k => (callerRow f c0 p0 k).start) (finish := fun k => (callerRow f c0 p0 k).finish) m
    fun k _ => by
      simp only [callerRow]
      rw [UnifiedRow.finish_start _ _ _ (previousOf p0 c0 (k + 1))]
      congr 2

/-- Every caller's decoder query is a row of the caller table of `program f n`. -/
theorem decoded (room : Room f c0 p0 n) : ∀ row ∈ callerRows f c0 p0 n,
    (Delegation.Caller.rvDecoderTable (p := P) (program f n)).Contains #[] (UnifiedReduced.decoderQuery row.assignment) := by
  intro row member
  obtain ⟨k, small, rfl⟩ := mem_rows member
  refine ⟨⟨k, by simpa [program, callerPCs] using small⟩, ?_⟩
  simp only [program, callerPCs, List.get_eq_getElem, List.getElem_map, List.getElem_range]
  exact UnifiedRow.query (f + 4 * k) (c0 + 4 * k) (previousOf p0 c0 k) (by have := room.pc; omega)

end Airbender.NonVacuous.HashCallers.UnifiedBlock
