module
public import Slop.NonVacuous.FamilyCallers.Row

@[expose] public section

/-! A block of `n` unified caller rows of family `g`: caller `k` at PC `f + 4 k` and clock `c0 + 4 k`, reading x0 as
    the previous caller left it (the first caller: as written at `p0`). Every fact is one statement over the block,
    from the one-row lemmas of `Row.lean`: the rows satisfy the unified constraints, are the selected callers, issue
    the family's requests at `c0 + 4 k + 1`, decode in the caller table of `program g f n`, chain their PC/clock
    states, and their x0 ports are the x0 chain's edges. -/

namespace Airbender.NonVacuous.FamilyCallers.Block
open Trace HashCallers

local notation "P" => babyBearModulus

def callerRow (g : Delegation.Family) (f c0 p0 k : Nat) : Row P UnifiedFamily :=
  CallerRow.row g (f + 4 * k) (c0 + 4 * k) (previousOf p0 c0 k)

def callerRows (g : Delegation.Family) (f c0 p0 n : Nat) : List (Row P UnifiedFamily) :=
  (List.range n).map (callerRow g f c0 p0)

/-- Room for the block's PCs and clocks; the first caller's x0 was written before its clock. -/
structure Room (f c0 p0 n : Nat) : Prop where
  pc : f + 4 * n < 65536
  clock : c0 + 4 * n < timestampBase
  previous : p0 < c0

variable {g : Delegation.Family} {f c0 p0 n : Nat}

theorem mem_rows {row : Row P UnifiedFamily} (member : row ∈ callerRows g f c0 p0 n) :
    ∃ k < n, row = callerRow g f c0 p0 k := by
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  exact ⟨k, List.mem_range.mp present, rfl⟩

theorem valid (room : Room f c0 p0 n) {k : Nat} (small : k < n) :
    CallerRow.Valid (f + 4 * k) (c0 + 4 * k) (previousOf p0 c0 k) := by
  have := room.pc
  have := room.clock
  have := room.previous
  refine ⟨by omega, by omega, ?_⟩
  unfold previousOf
  split <;> omega

theorem satisfies (room : Room f c0 p0 n) (before : RV.State) : ∀ row ∈ callerRows g f c0 p0 n,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints (UnifiedReduced.Setup.tableRV (p := P) before)) := by
  intro row member
  obtain ⟨k, small, rfl⟩ := mem_rows member
  exact CallerRow.satisfies (valid room small) before

theorem active : ∀ row ∈ callerRows g f c0 p0 n, row.assignment row.columns.execute = 1 := by
  intro row member
  obtain ⟨k, -, rfl⟩ := mem_rows member
  exact CallerRow.active ..

theorem selected : ∀ row ∈ callerRows g f c0 p0 n, UnifiedReduced.Caller.Selected row.assignment := by
  intro row member
  obtain ⟨k, -, rfl⟩ := mem_rows member
  exact CallerRow.selected ..

/-- Every row of the block is a selected caller. -/
theorem filter_selected :
    (callerRows g f c0 p0 n).filter (fun row => decide (UnifiedReduced.Caller.Selected row.assignment)) =
      callerRows g f c0 p0 n :=
  List.filter_eq_self.mpr fun row member => decide_eq_true (selected row member)

theorem requests : (callerRows g f c0 p0 n).map (fun row => UnifiedReduced.Caller.request row.assignment) =
    (List.range n).map (requestAt g c0) := by
  rw [callerRows, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, callerRow, CallerRow.request, requestAt]
  congr 3
  omega

theorem edges : (callerRows g f c0 p0 n).flatMap (fun row => (UnifiedReduced.Caller.machinePorts row).toList.map
      (fun port => (readToken row.assignment port, writeToken row.columns row.assignment port))) =
    (List.range n).flatMap (fun k => x0Edges (previousOf p0 c0 k) (c0 + 4 * k)) := by
  rw [callerRows, List.flatMap_map]
  exact List.flatMap_congr fun k _ => CallerRow.steps ..

/-- The block's PC/clock states chain from its first start to its last finish. -/
theorem states (m : Nat) :
    ((callerRow g f c0 p0 0).start :: (callerRows g f c0 p0 (m + 1)).map Row.finish).Perm
      ((callerRow g f c0 p0 m).finish :: (callerRows g f c0 p0 (m + 1)).map Row.start) := by
  simp only [callerRows, List.map_map]
  exact chain_perm (start := fun k => (callerRow g f c0 p0 k).start) (finish := fun k => (callerRow g f c0 p0 k).finish) m
    fun k _ => by
      simp only [callerRow]
      rw [CallerRow.finish_start _ _ _ _ (previousOf p0 c0 (k + 1))]
      congr 2

/-- Every caller's decoder query is a row of the caller table of `program g f n`. -/
theorem decoded (room : Room f c0 p0 n) : ∀ row ∈ callerRows g f c0 p0 n,
    (Delegation.Caller.rvDecoderTable (p := P) (program g f n)).Contains #[] (UnifiedReduced.decoderQuery row.assignment) := by
  intro row member
  obtain ⟨k, small, rfl⟩ := mem_rows member
  refine ⟨⟨k, by simpa [program, callerPCs] using small⟩, ?_⟩
  simp only [program, callerPCs, List.get_eq_getElem, List.getElem_map, List.getElem_range]
  exact CallerRow.query g (f + 4 * k) (c0 + 4 * k) (previousOf p0 c0 k) (by have := room.pc; omega)

end Airbender.NonVacuous.FamilyCallers.Block
