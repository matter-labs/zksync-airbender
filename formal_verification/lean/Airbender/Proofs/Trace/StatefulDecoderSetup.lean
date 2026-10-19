import Airbender.Review.Helpers.Decoder.StatefulSetup
import Airbender.Proofs.Trace.SparseDecoderSetup
import Airbender.Proofs.Sail.DecoderFrame

namespace Airbender.Trace.Proofs

theorem run_entry_source {Kind : Type} {before : Reference.RiscV.Sail.State} {pc : BitVec 32}
    {entry : ProgramEntry Kind}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (image : programEntryRunWith projection before pc = some entry) :
    entry.pc = pc ∧ entry.SourceWith before projection := by
  unfold programEntryRunWith at image
  cases read : (Cell.ram pc).read before with
  | error error after => simp [read, bind, Option.bind] at image
  | ok bits after =>
    have frame := cell_read_frame (.ram pc) read
    subst after
    simp only [read, bind, Option.bind] at image
    cases decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards bits) before with
    | error error after => simp [decoded] at image
    | ok instruction after =>
      simp only [decoded] at image
      cases fields : projection instruction with
      | none => simp [fields] at image
      | some data =>
        simp only [fields, pure, Option.some.injEq] at image
        subst entry
        exact ⟨rfl, ⟨read, (Reference.Sail.decoded_misa_frame _ decoded).2 before rfl, fields⟩⟩

/-- Selecting a supported sparse slot retains the original strict entry builder. -/
theorem run_slot_selected {Kind : Type} {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {pc : BitVec 32} {entry : ProgramEntry Kind}
    (built : programSlotRunWith projection before pc = some (some entry)) :
    programEntryRunWith projection before pc = some entry := by
  unfold programSlotRunWith programEntryRunWith at *
  cases read : (Cell.ram pc).read before with
  | error _ _ => simp [read, bind, Option.bind] at built
  | ok bits after =>
    simp only [read, bind, Option.bind] at *
    cases decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards bits) before with
    | error _ _ => simp [decoded] at built
    | ok instruction after =>
      simp only [decoded] at *
      cases fields : projection instruction with
      | none => simp [fields, pure] at built
      | some data => simpa [fields, pure] using built

/-- Keep actual indexed source locations rather than compacting supported words. -/
theorem run_slots_selected {Kind : Type} {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {slots : List (Option (ProgramEntry Kind))}
    (image : addresses.mapM (programSlotRunWith projection before) = some slots)
    {entry : ProgramEntry Kind} (member : some entry ∈ slots) :
    ∃ pc ∈ addresses, programEntryRunWith projection before pc = some entry := by
  induction addresses generalizing slots with
  | nil => simp [List.mapM_nil, pure] at image; subst slots; cases member
  | cons address addresses ih =>
    rw [List.mapM_cons] at image
    cases first : programSlotRunWith projection before address with
    | none => simp [first, bind, Option.bind] at image
    | some slot =>
      cases rest : addresses.mapM (programSlotRunWith projection before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some tail =>
        simp only [first, rest, bind, Option.bind, pure, Option.some.injEq] at image
        subst slots
        rcases List.mem_cons.mp member with same | later
        · subst slot
          exact ⟨address, by simp, run_slot_selected first⟩
        · obtain ⟨pc, present, built⟩ := ih rest later
          exact ⟨pc, by simp [present], built⟩

theorem run_sparse_setup_selected {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    {setup : SparseDecoderSetup Kind}
    (image : sparseDecoderSetupImageRunWith projection before count logCapacity = some setup)
    {entry : ProgramEntry Kind} (member : entry ∈ setup.program) :
    ∃ i < count, programEntryRunWith projection before (BitVec.ofNat 32 (4 * i)) = some entry := by
  unfold sparseDecoderSetupImageRunWith at image
  split at image
  · cases slots : ((List.range count).map fun i => BitVec.ofNat 32 (4 * i)).mapM
        (programSlotRunWith projection before) with
    | none => simp [slots] at image
    | some entries =>
      simp only [slots, bind, Option.bind, pure, Option.some.injEq] at image
      subst setup
      have present : some entry ∈ entries := by simpa [SparseDecoderSetup.program] using member
      obtain ⟨pc, location, built⟩ := run_slots_selected slots present
      obtain ⟨i, bound, rfl⟩ := List.mem_map.mp location
      exact ⟨i, List.mem_range.mp bound, built⟩
  · cases image

theorem run_sparse_setup_sources {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat} {setup : SparseDecoderSetup Kind}
    (image : sparseDecoderSetupImageRunWith projection before count logCapacity = some setup)
    {entry : ProgramEntry Kind} (member : entry ∈ setup.program) :
    entry.SourceWith before projection ∧
      (Arithmetic.Word.ofBitVec entry.pc).lo % 4 = 0 := by
  obtain ⟨i, _, built⟩ := run_sparse_setup_selected image member
  obtain ⟨pc, source⟩ := run_entry_source built
  exact ⟨source, by rw [pc]; exact indexed_pc_aligned i⟩


/-- The first supported slot is retained independently of holes and capacity. -/
theorem sparse_head_member {Kind : Type} {p : Nat} [Fact p.Prime]
    (entry : ProgramEntry Kind) (tail : List (Option (ProgramEntry Kind))) (padding : Nat) :
    ((SparseDecoderSetup.mk (some entry :: tail) padding).table (p := p)).Contains #[] entry.query := by
  refine ⟨⟨0,by simp⟩,rfl⟩

/-- Every index beyond the public slot prefix is exactly the native sentinel.
    Use the list-length bound rather than reducing a large concrete index. -/
theorem sparse_row_absent {Kind : Type} {p : Nat} (setup : SparseDecoderSetup Kind)
    (i : Fin (setup.slots.length + setup.padding)) (absent : setup.slots.length ≤ i.val) :
    setup.row (p := p) i = Vector.replicate 10 (-1) := by
  have missing : setup.slots[i.val]? = none := List.getElem?_eq_none absent
  simp only [SparseDecoderSetup.row,missing,Option.bind_none]

end Airbender.Trace.Proofs
