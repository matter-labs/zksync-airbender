import Airbender.Review.Helpers.Decoder.SparseSetup
import Airbender.Proofs.Trace.Program

namespace Airbender.Trace.Proofs

/-- Selecting a supported sparse slot retains the original strict entry builder. -/
theorem slot_selected {Kind : Type} {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {pc : BitVec 32} {entry : ProgramEntry Kind}
    (built : programSlotWith projection before pc = some (some entry)) :
    programEntryWith projection before pc = some entry := by
  unfold programSlotWith programEntryWith at *
  cases read : (Cell.ram pc).read before with
  | error _ _ => simp [read, bind, Option.bind] at built
  | ok bits after =>
    simp only [read, bind, Option.bind] at *
    cases decoded : SailRV32.Functions.encdec_backwards bits with
    | impure _ _ => simp [decoded] at built
    | pure instruction =>
      simp only [decoded] at *
      cases fields : projection instruction with
      | none => simp [fields, pure] at built
      | some data => simpa [fields, pure] using built

/-- Keep actual indexed source locations rather than compacting supported words. -/
theorem slots_selected {Kind : Type} {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {slots : List (Option (ProgramEntry Kind))}
    (image : addresses.mapM (programSlotWith projection before) = some slots)
    {entry : ProgramEntry Kind} (member : some entry ∈ slots) :
    ∃ pc ∈ addresses, programEntryWith projection before pc = some entry := by
  induction addresses generalizing slots with
  | nil => simp [List.mapM_nil, pure] at image; subst slots; cases member
  | cons address addresses ih =>
    rw [List.mapM_cons] at image
    cases first : programSlotWith projection before address with
    | none => simp [first, bind, Option.bind] at image
    | some slot =>
      cases rest : addresses.mapM (programSlotWith projection before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some tail =>
        simp only [first, rest, bind, Option.bind, pure, Option.some.injEq] at image
        subst slots
        rcases List.mem_cons.mp member with same | later
        · subst slot
          exact ⟨address, by simp, slot_selected first⟩
        · obtain ⟨pc, present, built⟩ := ih rest later
          exact ⟨pc, by simp [present], built⟩

theorem sparse_setup_selected {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    {setup : SparseDecoderSetup Kind}
    (image : sparseDecoderSetupImageWith projection before count logCapacity = some setup)
    {entry : ProgramEntry Kind} (member : entry ∈ setup.program) :
    ∃ i < count, programEntryWith projection before (BitVec.ofNat 32 (4 * i)) = some entry := by
  unfold sparseDecoderSetupImageWith at image
  split at image
  · cases slots : ((List.range count).map fun i => BitVec.ofNat 32 (4 * i)).mapM
        (programSlotWith projection before) with
    | none => simp [slots] at image
    | some entries =>
      simp only [slots, bind, Option.bind, pure, Option.some.injEq] at image
      subst setup
      have present : some entry ∈ entries := by simpa [SparseDecoderSetup.program] using member
      obtain ⟨pc, location, built⟩ := slots_selected slots present
      obtain ⟨i, bound, rfl⟩ := List.mem_map.mp location
      exact ⟨i, List.mem_range.mp bound, built⟩
  · cases image

theorem sparse_setup_sources {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat} {setup : SparseDecoderSetup Kind}
    (image : sparseDecoderSetupImageWith projection before count logCapacity = some setup)
    {entry : ProgramEntry Kind} (member : entry ∈ setup.program) :
    entry.SourceWith before projection ∧
      SailRV32.Functions.encdec_backwards entry.bits = .pure entry.instruction ∧
      (Arithmetic.Word.ofBitVec entry.pc).lo % 4 = 0 := by
  obtain ⟨i, _, built⟩ := sparse_setup_selected image member
  obtain ⟨pc, source⟩ := entry_source built
  exact ⟨source, entry_decoder_pure built, by rw [pc]; exact indexed_pc_aligned i⟩

/-- Any non-sentinel member comes from an actual supported slot, wherever it occurs. -/
theorem sparse_member {Kind : Type} {p : Nat} [Fact p.Prime]
    {setup : SparseDecoderSetup Kind} {query : Vector (ZMod p) 10}
    (member : setup.table.Contains #[] query) (active : query ≠ Vector.replicate 10 (-1)) :
    ∃ entry ∈ setup.program, query = entry.query := by
  change ∃ i, query = setup.row i at member
  obtain ⟨i, same⟩ := member
  unfold SparseDecoderSetup.row at same
  cases slot : setup.slots[i.val]? with
  | none => simp [slot] at same; exact (active same).elim
  | some value =>
    cases value with
    | none => simp [slot] at same; exact (active same).elim
    | some entry =>
      simp only [slot, Option.bind_some] at same
      refine ⟨entry, ?_, same⟩
      have present : some entry ∈ setup.slots := List.mem_of_getElem? slot
      simpa [SparseDecoderSetup.program] using present

end Airbender.Trace.Proofs
