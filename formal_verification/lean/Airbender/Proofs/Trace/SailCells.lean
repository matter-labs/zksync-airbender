import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.Sail.RegisterState

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

theorem cell_write_readback (cell : Cell) (value : BitVec 32) (before : State)
    (zero : cell = .register 0 → value = 0) :
    ∃ after, run (cell.write value) before = .ok () after ∧
      cell.read after = .ok value after := by
  cases cell with
  | register index =>
    obtain ⟨after, written, _, read⟩ := gpr_write_readback index value before
      (fun equal => zero (by rw [equal]))
    exact ⟨after, written, read⟩
  | ram address =>
    exact ⟨wordWriteState before address.toNat value,
      write_word_state before address value, written_word_read before address.toNat value⟩

/-- Different aligned cells preserve each other's actual native reads. This
    handles register aliases separately from RAM byte-window disjointness. -/
theorem cell_write_frame {before after : State} {cell other : Cell} {value old : BitVec 32}
    (written : run (cell.write value) before = .ok () after)
    (different : other ≠ cell) (aligned : cell.Aligned) (otherAligned : other.Aligned)
    (read : other.read before = .ok old before) : other.read after = .ok old after := by
  cases cell with
  | register index =>
    cases other with
    | register reader =>
      exact gpr_write_other written (fun equal => different (by rw [equal])) read
    | ram address =>
      obtain ⟨result, execution, memory⟩ := gpr_write_memory index value before
      have same := (EStateM.Result.ok.inj (execution.symm.trans written)).2
      subst result
      exact read_word_frame memory read
  | ram address =>
    have same := (EStateM.Result.ok.inj
      ((write_word_state before address value).symm.trans written)).2
    subst after
    cases other with
    | register index =>
      exact rX_register_frame (before := before)
        (after := wordWriteState before address.toNat value) rfl index read
    | ram reader =>
      have differentAddress : reader.toNat ≠ address.toNat :=
        fun equal => different (by rw [BitVec.eq_of_toNat_eq equal])
      apply written_word_disjoint address.toNat value _ read
      change address.toNat % 4 = 0 at aligned
      change reader.toNat % 4 = 0 at otherAligned
      omega

theorem cell_write_same {before : State} {cell : Cell} {value : BitVec 32}
    (read : cell.read before = .ok value before) :
    run (cell.write value) before = .ok () before := by
  cases cell with
  | register index => exact gpr_write_same read
  | ram address =>
    change run (writeMemory (size := 4) address value) before = _
    rw [write_word_state, written_word_same read]

end Airbender.Trace.Proofs
