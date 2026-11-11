module
public import Slop.NonVacuous.HashCallers.Chain
public import Slop.NonVacuous.FamilyCallers.Program
public import Slop.NonVacuous.ClockCompleteness
public import Slop.UnifiedReduced.OpIndex
public import Slop.UnifiedReduced.ArtifactChecks
public import Slop.Constraints
public import Human.Helpers.UnifiedReduced.RVRequestTrace
public import Human.Helpers.UnifiedReduced.MixedMemory
public import Human.Circuits.UnifiedReduced.Tables.SetupRV
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The honest unified caller row of `csrrw x0, csr f, x0` (any delegation family `f`) at a PC and clock, x0 last
    written at a previous clock: it satisfies the unified equations, range and setup queries and clock queries for
    every family, PC, clock and previous clock in range (`satisfies`, proven once by constraint index), it is a
    selected caller issuing `(csr f, c + 1)`, its x0 ports are the chain's edges (`steps`), and its decoder query is
    the caller table's row of its PC. -/

namespace Airbender.NonVacuous.FamilyCallers.CallerRow
open Trace HashCallers

local notation "P" => babyBearModulus

/-- The columns: 0/30 PC and next PC, 2/32 clock and next clock, 34 the source port's previous clock, 46 the
    destination port's previous clock (the source port's write at `clock`), 4 execute, 18 the delegation selector,
    123–125 the clock-comparison borrows, 6/38 the CSR (rs2 field and the virtual port's address). -/
def column (f : Delegation.Family) (pc clock previous : Nat) (v : Nat) : Nat :=
  if v = 0 then pc else if v = 2 then clock else if v = 30 then pc + 4 else if v = 32 then clock + 4
  else if v = 34 then previous else if v = 46 then clock
  else if v = 4 then 1 else if v = 18 then 1 else if v = 123 then 1 else if v = 124 then 1 else if v = 125 then 1
  else if v = 6 then Delegation.Requests.csr f else if v = 38 then Delegation.Requests.csr f else 0

def assignment {p : Nat} (f : Delegation.Family) (pc clock previous : Nat) (v : Nat) : ZMod p :=
  (column f pc clock previous v : ZMod p)

def row (f : Delegation.Family) (pc clock previous : Nat) : Row P UnifiedFamily :=
  ⟨.machine, assignment f pc clock previous⟩

/-- The range of an honest caller row. -/
structure Valid (pc clock previous : Nat) : Prop where
  pcRoom : pc + 4 < 65536
  clockRoom : clock + 4 < timestampBase
  ordered : previous < clock

variable {p : Nat} [Fact p.Prime]

theorem asserts (f : Delegation.Family) (pc clock previous : Nat) (setup : Table (ZMod p) (fields 10)) :
    ∀ i (h : i < (FlatOperation.constraints (UnifiedReduced.importedConstraints setup)).length),
      ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup)).get ⟨i, h⟩).eval
        (Verification.environment (assignment f pc clock previous)) = 0 := by
  intro i h
  have size : i < 120 := by rwa [UnifiedReduced.constraint_count] at h
  interval_cases i <;> op_index <;>
    simp only [Expression.eval, Verification.environment, assignment, column] <;> push_cast <;> ring

/-- A setup query of zeros: the setup table's first row (tag zero), whatever the ROM words. -/
theorem zero_contains {words : Nat → BitVec 32} {entry : Vector (Expression (ZMod p)) 10} {env : Environment (ZMod p)}
    (zero : ∀ j : Fin 10, entry[j].eval env = 0) :
    (Lookup.mk (UnifiedReduced.Setup.tableWith (p := p) words).toRaw entry).Contains env := by
  refine ⟨⟨0, Nat.succ_pos _⟩, ?_⟩
  change entry.map (Expression.eval env) =
    (UnifiedReduced.Setup.rowWith words ⟨0, Nat.succ_pos _⟩).map (fun (n : Nat) => (n : ZMod p))
  have first : UnifiedReduced.Setup.rowWith words ⟨0, Nat.succ_pos _⟩ = #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [UnifiedReduced.Setup.rowWith, dite_eq_left (by decide)]
    decide
  rw [first]
  apply Vector.ext
  intro j hj
  have value := zero ⟨j, hj⟩
  simp only [Fin.getElem_fin] at value
  rw [Vector.getElem_map, Vector.getElem_map, value]
  interval_cases j <;> simp

theorem lookups {f : Delegation.Family} {pc clock previous : Nat} (valid : Valid pc clock previous) (before : RV.State) :
    ∀ i (h : i < (FlatOperation.lookups (UnifiedReduced.importedConstraints
        (UnifiedReduced.Setup.tableRV (p := P) before))).length),
      ((FlatOperation.lookups (UnifiedReduced.importedConstraints
        (UnifiedReduced.Setup.tableRV (p := P) before))).get ⟨i, h⟩).Contains
          (Verification.environment (assignment f pc clock previous)) := by
  have bound := valid.pcRoom
  intro i h
  have size : i < 18 := by rwa [UnifiedReduced.lookup_count] at h
  have zero (e : Expression (ZMod P)) (value : e.eval (Verification.environment (assignment f pc clock previous)) =
      ((0 : Nat) : ZMod P)) := range16_of_eval value (by decide)
  interval_cases i <;> op_index
  all_goals try (refine zero_contains fun j => ?_; fin_cases j <;>
    simp [Expression.eval, Verification.environment, assignment, column])
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact range16_of_eval (n := Delegation.Requests.csr f) (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring) (csr_lt f)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)
  · exact range16_of_eval (n := pc + 4) (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring) bound
  · exact zero _ (by simp only [Expression.eval, Verification.environment, assignment, column]; push_cast; ring)

theorem timestamps {f : Delegation.Family} {pc clock previous : Nat} (valid : Valid pc clock previous) :
    ∀ i (h : i < (FlatOperation.lookups (UnifiedReduced.importedConstraintsTimestampLookups (p := P))).length),
      ((FlatOperation.lookups (UnifiedReduced.importedConstraintsTimestampLookups (p := P))).get ⟨i, h⟩).Contains
        (Verification.environment (assignment f pc clock previous)) := by
  have room := valid.clockRoom
  have ordered := valid.ordered
  simp only [timestampBase] at room
  intro i h
  have size : i < 8 := by rwa [UnifiedReduced.timestamp_count] at h
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

/-- The honest caller row satisfies the unified machine's equations, queries and clock queries. -/
theorem satisfies {f : Delegation.Family} {pc clock previous : Nat} (valid : Valid pc clock previous) (before : RV.State) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment f pc clock previous))
      (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.tableRV (p := P) before)) := by
  refine Verification.holds_append (holds_of_get (asserts f pc clock previous _) (lookups valid before))
    (holds_of_get (fun i h => ?_) (timestamps valid))
  have empty : FlatOperation.constraints (UnifiedReduced.importedConstraintsTimestampLookups (p := P)) = [] := rfl
  rw [empty] at h
  exact absurd h (Nat.not_lt_zero i)

theorem active (f : Delegation.Family) (pc clock previous : Nat) : (row f pc clock previous).assignment (row f pc clock previous).columns.execute = 1 :=
  Nat.cast_one

theorem selected (f : Delegation.Family) (pc clock previous : Nat) : UnifiedReduced.Caller.Selected (row f pc clock previous).assignment :=
  Nat.cast_one

/-- The finish of a caller is the start of the next caller. -/
theorem finish_start (f : Delegation.Family) (pc clock previous next : Nat) :
    (row f pc clock previous).finish = (row f (pc + 4) (clock + 4) next).start := rfl

/-- The caller issues its family's request at `clock + 1`. -/
theorem request (f : Delegation.Family) (pc clock previous : Nat) :
    UnifiedReduced.Caller.request (row f pc clock previous).assignment =
      ⟨Delegation.Requests.csr f, (((clock + 1 : Nat) : ZMod P), ((0 : Nat) : ZMod P))⟩ := by
  show (⟨(((Delegation.Requests.csr f : Nat) : ZMod P)).val, (((clock : Nat) : ZMod P) + ((1 : Nat) : ZMod P), ((0 : Nat) : ZMod P))⟩ :
    Delegation.Requests.Request P) = _
  rw [ZMod.val_natCast_of_lt (Nat.lt_trans (csr_lt f) (by decide)), ← Nat.cast_add]

/-- The caller's x0 ports: the source port reads the token of `previous` and writes at `clock`, the destination
    port reads that write and writes at `clock + 2`. -/
theorem steps (f : Delegation.Family) (pc clock previous : Nat) :
    (UnifiedReduced.Caller.machinePorts (row f pc clock previous)).toList.map (fun port =>
      (readToken (row f pc clock previous).assignment port,
        writeToken (row f pc clock previous).columns (row f pc clock previous).assignment port)) =
      x0Edges previous clock := by
  rw [UnifiedReduced.Caller.machinePorts, ite_eq_left (selected f pc clock previous)]
  show ([(⟨Nat.pair 0 (Nat.pair (((0 : Nat) : ZMod P)).val 0), (((previous : Nat) : ZMod P), ((0 : Nat) : ZMod P)),
      Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val⟩,
    ⟨Nat.pair 0 (Nat.pair (((0 : Nat) : ZMod P)).val 0), (((clock : Nat) : ZMod P) + ((0 : Nat) : ZMod P), ((0 : Nat) : ZMod P)),
      Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val⟩),
    (⟨Nat.pair (((0 : Nat) : ZMod P)).val (Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val), (((clock : Nat) : ZMod P), ((0 : Nat) : ZMod P)),
      Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val⟩,
    ⟨Nat.pair (((0 : Nat) : ZMod P)).val (Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val), (((clock : Nat) : ZMod P) + ((2 : Nat) : ZMod P), ((0 : Nat) : ZMod P)),
      Nat.pair (((0 : Nat) : ZMod P)).val (((0 : Nat) : ZMod P)).val⟩)] : List (MemoryToken P × MemoryToken P)) = (_ : List (MemoryToken P × MemoryToken P))
  simp only [x0Edges, x0Token, Nat.cast_zero, add_zero, ZMod.val_zero, Nat.cast_add, Nat.cast_ofNat]
  rfl

/-- The selector flags' mask of any caller row: selector seven. -/
theorem flag_sum : (∑ i : Fin UnifiedReduced.importedConstraintsDecoderColumns.flags.size,
      ((2 ^ i.val : Nat) : ZMod P) * (row .blakeG 0 0 0).assignment
        UnifiedReduced.importedConstraintsDecoderColumns.flags[i]) = 128 := by decide +kernel

/-- The caller's decoder query is the caller table's row of its PC. -/
theorem query (f : Delegation.Family) (pc clock previous : Nat) (small : pc < 65536) :
    UnifiedReduced.decoderQuery (row f pc clock previous).assignment =
      Delegation.Caller.rvQuery (callerEntry f (BitVec.ofNat 32 pc)) := by
  have lo : (Arithmetic.Word.ofBitVec (BitVec.ofNat 32 pc)).lo = pc := by
    simp only [Arithmetic.Word.ofBitVec, BitVec.toNat_ofNat, Arithmetic.limbBase, Nat.reducePow]; omega
  have hi : (Arithmetic.Word.ofBitVec (BitVec.ofNat 32 pc)).hi = 0 := by
    simp only [Arithmetic.Word.ofBitVec, BitVec.toNat_ofNat, Arithmetic.limbBase, Nat.reducePow]; omega
  simp only [Delegation.Caller.rvQuery, callerEntry, lo, hi]
  have flags : (∑ i : Fin UnifiedReduced.importedConstraintsDecoderColumns.flags.size,
      ((2 ^ i.val : Nat) : ZMod P) * (row f pc clock previous).assignment
        UnifiedReduced.importedConstraintsDecoderColumns.flags[i]) = 128 := by
    have same (i : Fin UnifiedReduced.importedConstraintsDecoderColumns.flags.size) :
        (row f pc clock previous).assignment UnifiedReduced.importedConstraintsDecoderColumns.flags[i] =
          (row .blakeG 0 0 0).assignment UnifiedReduced.importedConstraintsDecoderColumns.flags[i] := by
      obtain ⟨i, h⟩ := i
      have h' : i < 19 := h
      interval_cases i <;> rfl
    simp only [same]
    exact flag_sum
  show #v[((pc : Nat) : ZMod P), ((0 : Nat) : ZMod P), ((0 : Nat) : ZMod P), ((Delegation.Requests.csr f : Nat) : ZMod P),
    ((0 : Nat) : ZMod P), ((0 : Nat) : ZMod P), ((0 : Nat) : ZMod P), ((0 : Nat) : ZMod P), _] = _
  rw [flags]
  rfl

end Airbender.NonVacuous.FamilyCallers.CallerRow
