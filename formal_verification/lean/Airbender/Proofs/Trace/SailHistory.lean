import Airbender.Proofs.Trace.SailCells
import Airbender.Review.Trace.MemoryHistory

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail

/-- Interpret Clean's injective value code as its canonical RV32 word. -/
def memoryWord (code : Nat) : BitVec 32 :=
  (Word.mk (Nat.unpair code).1 (Nat.unpair code).2).toBitVec

/-- A Sail state realizes the latest values of the existing Clean history.
    This is a representation relation, not another memory semantics. -/
def SailStateMatches (cells : List Cell) (history : TimestampSortedMemoryAccessList)
    (state : State) : Prop :=
  ∀ cell ∈ cells, cell.read state =
    .ok (memoryWord (MemoryAccessList.lastWriteValue history.val history.property cell.addressCode))
      state

private theorem last_write_unique (history : MemoryAccessList)
    (sorted : history.isTimestampSorted)
    (unique : (history.map (fun event => event.2.1)).Nodup)
    {event : MemoryAccess} (member : List.Mem event history) :
    MemoryAccessList.lastWriteValue history sorted event.2.1 = event.2.2.2 := by
  induction history with
  | nil => cases member
  | cons head rest ih =>
    obtain ⟨time, key, old, value⟩ := head
    rcases List.mem_cons.mp member with rfl | member
    · simp [MemoryAccessList.lastWriteValue]
    · have distinct : key ≠ event.2.1 := by
        have pair := List.nodup_cons.mp unique
        intro equal
        exact pair.1 (List.mem_map.mpr ⟨event, member, equal.symm⟩)
      simpa only [MemoryAccessList.lastWriteValue, if_neg distinct] using
        ih (List.Pairwise.of_cons sorted) (List.nodup_cons.mp unique).2 member

/-- The public Sail image, rather than a read-value premise, supplies the
    starting values for a seeded Clean history. -/
theorem initial_history_matches {p : Nat} {before : State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens)
    (domain : cells.Nodup) (seed : TimestampSortedMemoryAccessList)
    (permutation : seed.val.Perm
      (tokens.map fun token => (token.address, token.address, 0, token.value))) :
    SailStateMatches cells seed before := by
  have unique : (seed.val.map (fun event => event.2.1)).Nodup := by
    apply (permutation.map (fun event => event.2.1)).nodup_iff.mpr
    simpa only [List.map_map, Function.comp_def] using image_unique image domain
  intro cell member
  obtain ⟨token, present, value, read, equal⟩ := image_cell_source image cell member
  have eventMember : List.Mem (α := MemoryAccess)
      (token.address, token.address, 0, token.value) seed.val := by
    apply permutation.mem_iff.mpr
    exact List.mem_map.mpr ⟨token, present, rfl⟩
  have last := last_write_unique seed.val seed.property unique eventMember
  subst token
  change MemoryAccessList.lastWriteValue seed.val seed.property cell.addressCode = _ at last
  rw [last]
  simp only [Cell.initialToken, memoryWord, Nat.unpair_pair]
  change cell.read before = .ok (Word.ofBitVec value).toBitVec before
  rw [Word.ofBitVec_roundtrip]
  exact read

/-- Actual Sail reads and writes for a reverse-chronological Clean access list.
    The tail executes first, as in Clean's online-consistency definition. -/
inductive SailHistory (cells : List Cell) : List MemoryAccess → State → State → Prop where
  | nil (before) : SailHistory cells [] before before
  | cons {event : MemoryAccess} {rest before middle after}
      (past : SailHistory cells rest before middle)
      (cell : Cell) (member : cell ∈ cells) (address : cell.addressCode = event.2.1)
      (read : cell.read middle = .ok (memoryWord event.2.2.1) middle)
      (write : run (cell.write (memoryWord event.2.2.2)) middle = .ok () after) :
      SailHistory cells (event :: rest) before after

theorem history_configuration {cells : List Cell} {events : List MemoryAccess} {before after : State}
    (history : SailHistory cells events before after) (configuration : FlatMemoryConfiguration before) :
    FlatMemoryConfiguration after := by
  induction history with
  | nil => exact configuration
  | cons past cell member address read write ih =>
    exact cell_write_configuration (ih configuration) write

/-- One actual native write advances the representation of Clean's last-write
    function and preserves every other public, aligned cell. -/
theorem matches_after_write {cells : List Cell} {history : TimestampSortedMemoryAccessList}
    {before : State} (boundState : SailStateMatches cells history before)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (event : MemoryAccess) (sorted : MemoryAccessList.isTimestampSorted (event :: history.val))
    (cell : Cell) (member : cell ∈ cells) (address : cell.addressCode = event.2.1)
    (zero : cell = .register 0 → memoryWord event.2.2.2 = 0) :
    ∃ after, run (cell.write (memoryWord event.2.2.2)) before = .ok () after ∧
      SailStateMatches cells ⟨event :: history.val, sorted⟩ after := by
  obtain ⟨time, key, old, value⟩ := event
  obtain ⟨after, written, readback⟩ := cell_write_readback cell (memoryWord value) before zero
  refine ⟨after, written, ?_⟩
  intro other otherMember
  by_cases same : other = cell
  · subst other
    simpa [MemoryAccessList.lastWriteValue, address] using readback
  · have distinctCode : key ≠ other.addressCode := by
      intro sameCode
      exact same (cell_address_injective (sameCode.symm.trans address.symm))
    simpa only [MemoryAccessList.lastWriteValue, if_neg distinctCode] using
      cell_write_frame written same (aligned cell member) (aligned other otherMember)
        (boundState other otherMember)

/-- Extend an already-bound initial history using Clean consistency. Read
    values are derived, not additional premises. The remaining conditions only
    identify the public address domain, alignment and hardwired x0 writes. -/
theorem realize_history {cells : List Cell} (events : List MemoryAccess)
    (seed : TimestampSortedMemoryAccessList) {before : State}
    (boundState : SailStateMatches cells seed before)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (addresses : ∀ event ∈ events, ∃ cell ∈ cells, cell.addressCode = event.2.1)
    (zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0)
    (sorted : MemoryAccessList.isTimestampSorted (List.append (α := MemoryAccess) events seed.val))
    (consistent : MemoryAccessList.isConsistentOnline (List.append (α := MemoryAccess) events seed.val) sorted) :
    ∃ after, SailHistory cells events before after ∧
      SailStateMatches cells ⟨List.append (α := MemoryAccess) events seed.val, sorted⟩ after := by
  induction events with
  | nil => exact ⟨before, .nil before, boundState⟩
  | cons event rest ih =>
    have ordered := List.Pairwise.of_cons sorted
    change event.2.2.1 = MemoryAccessList.lastWriteValue (List.append (α := MemoryAccess) rest seed.val) ordered event.2.1 ∧
      MemoryAccessList.isConsistentOnline (List.append (α := MemoryAccess) rest seed.val) ordered at consistent
    obtain ⟨middle, past, bound⟩ := ih (fun e m => addresses e (List.mem_cons_of_mem _ m))
      (fun e m => zero e (List.mem_cons_of_mem _ m)) ordered consistent.2
    obtain ⟨cell, member, address⟩ := addresses event (List.mem_cons_self)
    have read := bound cell member
    rw [address, ← consistent.1] at read
    obtain ⟨after, written, last⟩ := matches_after_write bound aligned event sorted cell member address
      (fun same => zero event (List.mem_cons_self) (by rw [← address, same]))
    exact ⟨after, .cons past cell member address read written, last⟩

theorem history_register_readable {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after) (index : BitVec 5)
    (initialized : ∃ word, run (SailRV32.Functions.rX_bits (.Regidx index)) before = .ok word before) :
    ∃ word, run (SailRV32.Functions.rX_bits (.Regidx index)) after = .ok word after := by
  induction history with
  | nil => exact initialized
  | cons past cell member address read write ih =>
    exact cell_write_register_readable index (ih initialized) write

/-- Even source registers erased by x0 preprocessing remain readable from the
    public initial image. No expected operand value or per-row read is assumed. -/
theorem image_register_after_history {p : Nat} {cells : List Cell} {events : List MemoryAccess}
    {before after : State} {tokens : List (MemoryToken p)}
    (image : initialImage before cells = some tokens)
    (history : SailHistory cells events before after) (index : BitVec 5)
    (present : Cell.register index ∈ cells) :
    ∃ word, run (SailRV32.Functions.rX_bits (.Regidx index)) after = .ok word after := by
  obtain ⟨_, _, value, read, _⟩ := image_cell_source image (.register index) present
  exact history_register_readable history index ⟨value, read⟩

end Airbender.Trace.Proofs
