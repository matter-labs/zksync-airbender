module
public import Mathlib.Data.List.Sort
-- Clean's Mathlib/Lean imports for this file, re-exported so importers see what they saw through Clean
public import Init.Data.List.Find
public import Lean
public import Lean.Elab.Tactic
public import Lean.Meta
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Control.Monad.Writer

/-! # Offline memory checking (Clean `Clean.Utils.OfflineMemory`, pinned b41c196): memory accesses, timestamp-sorted
access lists and their online consistency; transcribed with proofs. Deviation: the circuit gadgets are omitted. -/

@[expose] public section

namespace Airbender

/--
  A memory access consists of an address, a read value, and a write value.
  The semantics are that at this address, we read the readValue, and then write the writeValue.
-/
@[reducible]
def MemoryAccess := ℕ × ℕ × ℕ × ℕ -- (timestamp, addr, readValue, writeValue)

/--
A memory list is canonically represented in reverse order, so that the most recent access is at the head of the list.
-/
@[reducible]
def MemoryAccessList := List MemoryAccess

abbrev timestamp_ordering (x y : MemoryAccess) := match x, y with
| (t2, _a2, _r2, _w2), (t1, _a1, _r1, _w1) => t1 < t2

/--
  A memory access list is timestamp sorted if the timestamps are strictly decreasing.

  This proposition indexes proof-dependent memory operations, so Lean must unfold
  it while checking implicit arguments.
-/
@[implicit_reducible]
def MemoryAccessList.isTimestampSorted (accesses : MemoryAccessList) : Prop :=
  accesses.Pairwise timestamp_ordering

def TimestampSortedMemoryAccessList := {accesses : MemoryAccessList // accesses.isTimestampSorted}

def MemoryAccessList.lastWriteValue (accesses : MemoryAccessList) (h : accesses.isTimestampSorted) (addr : ℕ) : ℕ := match accesses with
  -- initially the memory is all zero
  | [] => 0
  | (_t, addr', _readValue, writeValue) :: rest =>
    if addr' = addr then
      -- since the list is timestamp sorted, the first operation we find for this address is the most recent one
      writeValue
    else
      MemoryAccessList.lastWriteValue rest (List.Pairwise.of_cons h) addr

def MemoryAccessList.isConsistentOnline (accesses : MemoryAccessList) (h : accesses.isTimestampSorted) : Prop := match accesses with
  | [] => True -- no memory access is trivially consistent
  | (_timestamp, addr, readValue, _writeValue) :: rest =>
    -- here we need to check that the readValue is consistent with the previous writes to the same address
    readValue = MemoryAccessList.lastWriteValue rest (List.Pairwise.of_cons h) addr
    ∧ MemoryAccessList.isConsistentOnline rest (List.Pairwise.of_cons h)

/--
  Filter a memory access list to only include accesses to a specific address.
-/
def MemoryAccessList.filterAddress (accesses : MemoryAccessList) (addr : ℕ) : MemoryAccessList :=
  accesses.filter (fun (_timestamp, addr', _readValue, _writeValue) => addr' = addr)

/--
  A filtered sorted memory access list is sorted as well.
-/
theorem MemoryAccessList.filterAddress_sorted (accesses : MemoryAccessList)
    (h : accesses.isTimestampSorted) (addr : ℕ) :
    (MemoryAccessList.filterAddress accesses addr).isTimestampSorted := by
  simp only [isTimestampSorted]
  apply List.Pairwise.filter
  exact h

theorem MemoryAccessList.filterAddress_cons (head : MemoryAccess) (tail : MemoryAccessList) (addr : ℕ) :
    MemoryAccessList.filterAddress (head :: tail) addr =
    match head with
    | ⟨_t, a, _r, _w⟩ => ((if a = addr then
      (head :: (MemoryAccessList.filterAddress tail addr))
        else (MemoryAccessList.filterAddress tail addr))) := by
  obtain ⟨_t, a, _r, _w⟩ := head
  simp only [filterAddress, List.filter_cons]
  split_ifs <;> simp_all

/--
  A memory access list is consistent for a single address if the reads and writes to that address are consistent.
  This variant of the consistency check is simpler, and holds only when the array contains only accesses to a single address.
  This function checks the following:
  - the first memory access must read 0
  - for each pair of consecutive accesses, the read of the most recent access must equal the write of the previous access
-/
def MemoryAccessList.isConsistentSingleAddress (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted) : Prop := match accesses with
  -- no memory access is trivially consistent
  | [] => True
  -- if there's only one access, the read must be zero
  | (_timestamp, _addr, readValue, _writeValue) :: [] => readValue = 0
  -- if there are multiple accesses, the read of the most recent access must equal the write of the previous access
  | (_t2, _addr2, readValue2, _writeValue2) :: (t1, addr1, readValue1, writeValue1) :: rest =>
    readValue2 = writeValue1 ∧
    MemoryAccessList.isConsistentSingleAddress ((t1, addr1, readValue1, writeValue1) :: rest) (List.Pairwise.of_cons h_sorted)

/--
  If a memory access list contains only accesses to a single address, then the following two consistency are equivalent:
  - the online consistency check
  - the single address consistency check
-/
theorem MemoryAccessList.isConsistentSingleAddress_iff (accesses : MemoryAccessList) (addr : ℕ) (h_sorted : accesses.isTimestampSorted)
    (h_eq : accesses.all (fun (_t, addr', _readValue, _writeValue) => addr' = addr)) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    MemoryAccessList.isConsistentSingleAddress accesses h_sorted := by
  induction accesses with
  | nil => simp only [isConsistentOnline, isConsistentSingleAddress]
  | cons head tail ih =>
    constructor
    · intro h
      cases tail with
      | nil =>
        obtain ⟨t, a, r, w⟩ := head
        simp_all only [List.all_nil, isConsistentOnline, isConsistentSingleAddress, imp_self,
          implies_true, List.all_cons, Bool.and_true, decide_eq_true_eq, lastWriteValue, and_true]
      | cons head2 tail2 =>
        obtain ⟨t2, a2, r2, w2⟩ := head
        obtain ⟨t1, a1, r1, w1⟩ := head2
        simp [isConsistentOnline, isConsistentSingleAddress, lastWriteValue] at ⊢ h h_eq ih
        have h_sorted' : isTimestampSorted ((t1, a1, r1, w1) :: tail2) := by
          unfold isTimestampSorted at h_sorted
          exact List.Pairwise.of_cons h_sorted
        obtain ⟨h_eq1, h_eq2, h_eq3⟩ := h_eq
        specialize ih h_sorted' h_eq2 h_eq3
        rw [←ih]
        simp_all only [↓reduceIte, and_self, true_iff]
    · intro h
      cases tail with
      | nil =>
        obtain ⟨t, a, r, w⟩ := head
        simp_all only [List.all_nil, isConsistentOnline, isConsistentSingleAddress, imp_self,
          implies_true, List.all_cons, Bool.and_true, decide_eq_true_eq, lastWriteValue, and_true]
      | cons head2 tail2 =>
        obtain ⟨t2, a2, r2, w2⟩ := head
        obtain ⟨t1, a1, r1, w1⟩ := head2
        simp [isConsistentOnline, isConsistentSingleAddress, lastWriteValue] at ⊢ h h_eq ih
        have h_sorted' : isTimestampSorted ((t1, a1, r1, w1) :: tail2) := by
          unfold isTimestampSorted at h_sorted
          exact List.Pairwise.of_cons h_sorted
        obtain ⟨h_eq1, h_eq2, h_eq3⟩ := h_eq
        specialize ih h_sorted' h_eq2 h_eq3
        rw [ih]
        simp_all only [↓reduceIte, and_self]

/--
  The last write value for a specific address is the same whether we compute it on the full list
  or on the filtered list on that address.
-/
theorem MemoryAccessList.lastWriteValue_filter (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted) (addr : ℕ) (h_sorted' : ((MemoryAccessList.filterAddress accesses addr).isTimestampSorted))  :
    MemoryAccessList.lastWriteValue accesses h_sorted addr =
    MemoryAccessList.lastWriteValue (MemoryAccessList.filterAddress accesses addr) h_sorted' addr := by
  induction accesses with
  | nil =>
    simp only [filterAddress, List.filter_nil, lastWriteValue]
  | cons head tail ih =>
    obtain ⟨t, a, r, w⟩ := head
    simp [filterAddress, List.filter_cons, lastWriteValue] at ⊢ ih
    -- is the current address the one we are filtering for?
    by_cases h_addr : a = addr
    · simp_all only [↓reduceIte, lastWriteValue]
    · have h_sorted_tail : isTimestampSorted tail := by
        unfold isTimestampSorted at h_sorted
        exact List.Pairwise.of_cons h_sorted
      have h_sorted_tail' : (MemoryAccessList.filterAddress tail addr).isTimestampSorted := by
        simp only [filterAddress]
        apply List.Pairwise.filter
        exact h_sorted_tail
      specialize ih h_sorted_tail h_sorted_tail'
      simp only [h_addr, ↓reduceIte, ih]

/--
  If a memory access list is online consistent, then the filtered list for a specific address is
  online consistent as well.
-/
theorem MemoryAccessList.isConsistentOnline_filter_of_consistentOnline (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted)
    (h_consistent : MemoryAccessList.isConsistentOnline accesses h_sorted) (addr : ℕ) :
    MemoryAccessList.isConsistentOnline (MemoryAccessList.filterAddress accesses addr) (MemoryAccessList.filterAddress_sorted accesses h_sorted addr) := by
  induction accesses with
  | nil =>
    simp only [filterAddress, List.filter_nil, isConsistentOnline]
  | cons head tail ih =>
    obtain ⟨t, a, r, w⟩ := head
    simp [filterAddress, List.filter_cons, isConsistentOnline] at ⊢ h_consistent ih
    have h_sorted' : isTimestampSorted tail := by
      unfold isTimestampSorted at h_sorted
      exact List.Pairwise.of_cons h_sorted
    -- is the current address the one we are filtering for?
    by_cases h_addr : a = addr
    ·
      specialize ih h_sorted' (And.right h_consistent)
      simp [h_addr, isConsistentOnline, ih]
      have h := MemoryAccessList.lastWriteValue_filter
      simp [h_consistent.left]
      rw [MemoryAccessList.lastWriteValue_filter]
      · simp [filterAddress, h_addr]
      · have h_sorted_tail' : (MemoryAccessList.filterAddress tail addr).isTimestampSorted := by
          simp only [filterAddress]
          apply List.Pairwise.filter
          exact h_sorted'
        rw [h_addr]
        exact h_sorted_tail'
    · simp_all only [forall_const, forall_true_left, ↓reduceIte]

theorem MemoryAccessList.isConsistentSingleAddress_cons (head : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : isTimestampSorted (head :: tail)) (h_sorted' : tail.isTimestampSorted)
    (h : isConsistentSingleAddress (head :: tail) h_sorted) :
    isConsistentSingleAddress tail h_sorted' := by
  obtain ⟨t_head, a_head, r_head, w_head⟩ := head
  cases tail with
  | nil =>
    simp_all [isConsistentSingleAddress]
  | cons head2 tail2 =>
    obtain ⟨t1, a1, r1, w1⟩ := head2
    simp_all [isConsistentSingleAddress]

theorem MemoryAccessList.isConsistentSingleAddress_cons_forall (head : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : isTimestampSorted (head :: tail))
    : (∀ addr : ℕ, (filterAddress (head :: tail) addr).isConsistentSingleAddress (MemoryAccessList.filterAddress_sorted (head :: tail) h_sorted addr)) →
    (∀ addr : ℕ, isConsistentSingleAddress (filterAddress tail addr) (MemoryAccessList.filterAddress_sorted tail (by simp_all only [isTimestampSorted,
      List.pairwise_cons]) addr)) := by
  intro h addr'
  obtain ⟨t_head, a_head, r_head, w_head⟩ := head
  simp_all [MemoryAccessList.filterAddress_cons]
  specialize h addr'
  by_cases h_addr : a_head = addr'
  · simp_all only [↓reduceIte]
    rw [h_addr] at h_sorted
    have tail_sorted : tail.isTimestampSorted := by
      unfold isTimestampSorted at h_sorted
      exact List.Pairwise.of_cons h_sorted
    have filtered_tail_sorted : (MemoryAccessList.filterAddress tail addr').isTimestampSorted := by
      simp only [filterAddress]
      apply List.Pairwise.filter
      exact tail_sorted

    have filter_eq_head : MemoryAccessList.filterAddress (⟨t_head, addr', r_head, w_head⟩ :: tail) addr' =
      (⟨t_head, addr', r_head, w_head⟩ :: (MemoryAccessList.filterAddress tail addr')) := by
      simp only [filterAddress, decide_true, List.filter_cons_of_pos]

    have h_filtered_sorted : MemoryAccessList.isTimestampSorted (⟨t_head, addr', r_head, w_head⟩ :: (MemoryAccessList.filterAddress tail addr')) := by
      rw [←filter_eq_head]
      apply MemoryAccessList.filterAddress_sorted
      assumption

    have h' := MemoryAccessList.isConsistentSingleAddress_cons ⟨t_head, addr', r_head, w_head⟩ (tail.filterAddress addr') h_filtered_sorted filtered_tail_sorted
    specialize h' h
    simp_all only
  · simp_all only [↓reduceIte]

/--
  A memory access list is consistent if and only if, for each possible address, considering
  only the accesses to that address, the single address consistency check holds.
-/
theorem MemoryAccessList.isConsistent_iff_all_single_address (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    (∀ addr : ℕ, MemoryAccessList.isConsistentSingleAddress (MemoryAccessList.filterAddress accesses addr) (MemoryAccessList.filterAddress_sorted accesses h_sorted addr)) := by
  constructor
  · intro h addr
    have h' := MemoryAccessList.isConsistentSingleAddress_iff (accesses.filterAddress addr) addr (MemoryAccessList.filterAddress_sorted accesses h_sorted addr)
        (by simp only [filterAddress, List.all_filter, Bool.not_or_self, List.all_eq_true,
          implies_true])
    exact h'.mp (MemoryAccessList.isConsistentOnline_filter_of_consistentOnline accesses h_sorted h addr)
  · intro h
    -- by induction on the list of accesses
    induction accesses with
    | nil =>
      simp [isConsistentOnline]
    | cons head tail ih =>
      obtain ⟨t, a, r, w⟩ := head
      have h_sorted' : isTimestampSorted tail := by
        unfold isTimestampSorted at h_sorted
        exact List.Pairwise.of_cons h_sorted
      specialize ih h_sorted'
      have h_tail := MemoryAccessList.isConsistentSingleAddress_cons_forall (t, a, r, w) tail h_sorted h
      specialize ih h_tail
      simp only [isConsistentOnline, ih, and_true]

      have h_tail_filter_sorted : (MemoryAccessList.filterAddress tail a).isTimestampSorted := by
        simp only [filterAddress]
        apply List.Pairwise.filter
        exact h_sorted'

      have h_filtered_sorted : MemoryAccessList.isTimestampSorted ((t, a, r, w) :: (MemoryAccessList.filterAddress tail a)) := by
        simp only [isTimestampSorted, List.pairwise_cons, filterAddress, List.mem_filter,
          and_imp] at ⊢ h_sorted
        simp_all only [implies_true, true_and]
        apply List.Pairwise.filter
        assumption

      have h' := MemoryAccessList.lastWriteValue_filter tail h_sorted' a h_tail_filter_sorted

      specialize h a
      simp [filterAddress_cons] at h
      -- rw [h']

      have h_iff := MemoryAccessList.isConsistentSingleAddress_iff ((t, a, r, w) :: filterAddress tail a) a h_filtered_sorted
      simp only [filterAddress, List.all_cons, decide_true, List.all_filter, Bool.not_or_self,
        Bool.true_and, List.all_eq_true, implies_true, forall_const] at h_iff
      have is_consistent_online_full := h_iff.mpr h
      simp only [isConsistentOnline] at is_consistent_online_full
      simp only [is_consistent_online_full.left]
      rw [eq_comm]
      apply MemoryAccessList.lastWriteValue_filter

end Airbender
