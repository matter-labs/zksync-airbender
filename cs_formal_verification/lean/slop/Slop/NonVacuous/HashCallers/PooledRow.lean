module
public import Slop.NonVacuous.HashCallers.Chain
public import Slop.NonVacuous.HashCallers.Program
public import Slop.NonVacuous.ClockCompleteness
public import Slop.AddSub.OpIndex
public import Slop.AddSub.ArtifactChecks
public import Slop.Constraints
public import Human.Helpers.Delegation.RVRequestTrace
public import Human.Helpers.Delegation.SharedMemory
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The honest ADD/SUB caller row of `csrrw x0, 0x7C8, x0` (six-family machine) at a PC and clock, x0 last written
    at a previous clock: as `UnifiedRow.lean` for the ADD/SUB circuit — it satisfies the equations, range queries and
    clock queries for every PC, clock and previous clock in range (`satisfies`, proven once by constraint index), it
    is a selected caller issuing `(0x7C8, c + 1)`, its x0 ports are the chain's edges (`steps`), and its decoder query
    is the caller table's row of its PC. -/

namespace Airbender.NonVacuous.HashCallers.PooledRow
open Trace

local notation "P" => babyBearModulus

/-- The columns: 0/19 PC and next PC, 2/21 clock and next clock, 23 the source port's previous clock, 35 the
    destination port's previous clock (the source port's write at `clock`), 4 execute, 17 the delegation selector,
    42–44 the clock-comparison borrows, 6 the CSR (rs2 field). -/
def column (pc clock previous : Nat) (v : Nat) : Nat :=
  if v = 0 then pc else if v = 2 then clock else if v = 19 then pc + 4 else if v = 21 then clock + 4
  else if v = 23 then previous else if v = 35 then clock
  else if v = 4 then 1 else if v = 17 then 1 else if v = 42 then 1 else if v = 43 then 1 else if v = 44 then 1
  else if v = 6 then 0x7C8 else 0

def assignment {p : Nat} (pc clock previous : Nat) (v : Nat) : ZMod p := (column pc clock previous v : ZMod p)

def row (pc clock previous : Nat) : Row P PooledFamily := ⟨.addSub, assignment pc clock previous⟩

/-- The range of an honest caller row. -/
structure Valid (pc clock previous : Nat) : Prop where
  pcRoom : pc + 4 < 65536
  clockRoom : clock + 4 < timestampBase
  ordered : previous < clock

variable {p : Nat} [Fact p.Prime]

theorem asserts (pc clock previous : Nat) :
    ∀ i (h : i < (FlatOperation.constraints (AddSub.importedConstraints (p := p))).length),
      ((FlatOperation.constraints (AddSub.importedConstraints (p := p))).get ⟨i, h⟩).eval
        (Verification.environment (assignment pc clock previous)) = 0 := by
  intro i h
  have size : i < 30 := by rwa [AddSub.constraint_count] at h
  interval_cases i <;> op_index <;>
    simp only [Expression.eval, Verification.environment, assignment, column] <;> push_cast <;> ring

theorem lookups {pc clock previous : Nat} (valid : Valid pc clock previous) :
    ∀ i (h : i < (FlatOperation.lookups (AddSub.importedConstraints (p := P))).length),
      ((FlatOperation.lookups (AddSub.importedConstraints (p := P))).get ⟨i, h⟩).Contains
        (Verification.environment (assignment pc clock previous)) := by
  have bound := valid.pcRoom
  have zero (e : Expression (ZMod P)) (value : e.eval (Verification.environment (assignment pc clock previous)) =
      ((0 : Nat) : ZMod P)) := range16_of_eval value (by decide)
  intro i h
  have size : i < 6 := by rwa [AddSub.lookup_count] at h
  interval_cases i <;> op_index
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact range16_of_eval (n := pc + 4) (by
      simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring) bound
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)

theorem timestamps {pc clock previous : Nat} (valid : Valid pc clock previous) :
    ∀ i (h : i < (FlatOperation.lookups (AddSub.importedConstraintsTimestampLookups (p := P))).length),
      ((FlatOperation.lookups (AddSub.importedConstraintsTimestampLookups (p := P))).get ⟨i, h⟩).Contains
        (Verification.environment (assignment pc clock previous)) := by
  have room := valid.clockRoom
  have ordered := valid.ordered
  simp only [timestampBase] at room
  intro i h
  have size : i < 8 := by rwa [AddSub.timestamp_count] at h
  have large : timestampBase ≤ P := by decide
  interval_cases i <;> op_index
  · exact range_of_eval (n := clock + 4) (by
      simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
      (by simp only [timestampBase]; omega) large
  · exact range_of_eval (n := 0) (by
      simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
      (by decide) large
  · exact range_of_eval (n := 524288 + previous - clock) (by
      simp only [Expression.eval, Verification.environment, assignment, column]
      rw [Nat.cast_sub (by omega)]; push_cast; ring) (by simp only [timestampBase]; omega) large
  · exact range_of_eval (n := 524287) (by
      simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
      (by decide) large
  · exact range_of_eval (n := 524287 - clock) (by
      simp only [Expression.eval, Verification.environment, assignment, column]
      rw [Nat.cast_sub (by omega)]; push_cast; ring) (by simp only [timestampBase]; omega) large
  · exact range_of_eval (n := 524287) (by
      simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
      (by decide) large
  · exact range_of_eval (n := 524286) (by
      simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
      (by decide) large
  · exact range_of_eval (n := 524287) (by
      simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
      (by decide) large

/-- The honest caller row satisfies the ADD/SUB circuit's equations, range queries and clock queries. -/
theorem satisfies {pc clock previous : Nat} (valid : Valid pc clock previous) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment pc clock previous))
      (AddSub.clockConstraints (p := P)) := by
  refine Verification.holds_append (holds_of_get (asserts pc clock previous) (lookups valid))
    (holds_of_get (fun i h => ?_) (timestamps valid))
  have empty : FlatOperation.constraints (AddSub.importedConstraintsTimestampLookups (p := P)) = [] := rfl
  rw [empty] at h
  exact absurd h (Nat.not_lt_zero i)

theorem active (pc clock previous : Nat) : (row pc clock previous).assignment (row pc clock previous).columns.execute = 1 :=
  Nat.cast_one

theorem selected (pc clock previous : Nat) : Delegation.Requests.Selected (row pc clock previous).assignment :=
  Nat.cast_one

/-- The finish of a caller is the start of the next caller. -/
theorem finish_start (pc clock previous next : Nat) :
    (row pc clock previous).finish = (row (pc + 4) (clock + 4) next).start := rfl

/-- The caller issues the G request at `clock + 1`. -/
theorem request (pc clock previous : Nat) : Delegation.Requests.caller (row pc clock previous).assignment =
    ⟨Delegation.Requests.csr .blakeG, (((clock + 1 : Nat) : ZMod P), ((0 : Nat) : ZMod P))⟩ := by
  show (⟨(((0x7C8 : Nat) : ZMod P)).val, (((clock : Nat) : ZMod P) + ((1 : Nat) : ZMod P), ((0 : Nat) : ZMod P))⟩ :
    Delegation.Requests.Request P) = _
  rw [ZMod.val_natCast_of_lt (by decide), ← Nat.cast_add]
  rfl

/-- The caller's x0 ports: the source port reads the token of `previous` and writes at `clock`, the destination
    port reads that write and writes at `clock + 2`. -/
theorem steps (pc clock previous : Nat) :
    Delegation.Caller.architecturalSteps (row pc clock previous).assignment = x0Edges previous clock := by
  show ([(⟨Nat.pair 0 (Nat.pair (((0 : Nat) : ZMod P)).val 0), (((previous : Nat) : ZMod P), ((0 : Nat) : ZMod P)),
      Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val⟩,
    ⟨Nat.pair 0 (Nat.pair (((0 : Nat) : ZMod P)).val 0),
      (((clock : Nat) : ZMod P) + ((0 : Nat) : ZMod P), ((0 : Nat) : ZMod P)),
      Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val⟩),
    (⟨Nat.pair 0 (Nat.pair (((0 : Nat) : ZMod P)).val 0), (((clock : Nat) : ZMod P), ((0 : Nat) : ZMod P)),
      Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val⟩,
    ⟨Nat.pair 0 (Nat.pair (((0 : Nat) : ZMod P)).val 0),
      (((clock : Nat) : ZMod P) + ((2 : Nat) : ZMod P), ((0 : Nat) : ZMod P)),
      Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val⟩)] :
    List (MemoryToken P × MemoryToken P)) = _
  simp only [x0Edges, x0Token, Nat.cast_zero, add_zero, ZMod.val_zero, Nat.cast_add, Nat.cast_ofNat]
  rfl

/-- The selector flags' mask of any caller row: selector seven. -/
theorem flag_sum : (∑ i : Fin AddSub.importedConstraintsDecoderColumns.flags.size,
      ((2 ^ i.val : Nat) : ZMod P) * (row 0 0 0).assignment AddSub.importedConstraintsDecoderColumns.flags[i]) =
    128 := by decide +kernel

/-- The caller's decoder query is the caller table's row of its PC. -/
theorem query (pc clock previous : Nat) (small : pc < 65536) :
    Delegation.Caller.nativeQuery (row pc clock previous).assignment =
      Delegation.Caller.rvQuery (callerEntry (BitVec.ofNat 32 pc)) := by
  have lo : (Arithmetic.Word.ofBitVec (BitVec.ofNat 32 pc)).lo = pc := by
    simp only [Arithmetic.Word.ofBitVec, BitVec.toNat_ofNat, Arithmetic.limbBase, Nat.reducePow]; omega
  have hi : (Arithmetic.Word.ofBitVec (BitVec.ofNat 32 pc)).hi = 0 := by
    simp only [Arithmetic.Word.ofBitVec, BitVec.toNat_ofNat, Arithmetic.limbBase, Nat.reducePow]; omega
  simp only [Delegation.Caller.rvQuery, callerEntry, lo, hi]
  have flags : (∑ i : Fin AddSub.importedConstraintsDecoderColumns.flags.size,
      ((2 ^ i.val : Nat) : ZMod P) * (row pc clock previous).assignment
        AddSub.importedConstraintsDecoderColumns.flags[i]) = 128 := by
    have same (i : Fin AddSub.importedConstraintsDecoderColumns.flags.size) :
        (row pc clock previous).assignment AddSub.importedConstraintsDecoderColumns.flags[i] =
          (row 0 0 0).assignment AddSub.importedConstraintsDecoderColumns.flags[i] := by
      obtain ⟨i, h⟩ := i
      have h' : i < 9 := h
      interval_cases i <;> rfl
    simp only [same]
    exact flag_sum
  show #v[((pc : Nat) : ZMod P), ((0 : Nat) : ZMod P), ((0 : Nat) : ZMod P), ((0x7C8 : Nat) : ZMod P),
    ((0 : Nat) : ZMod P), ((0 : Nat) : ZMod P), ((0 : Nat) : ZMod P), 0, _] = _
  rw [flags]
  rfl

end Airbender.NonVacuous.HashCallers.PooledRow
