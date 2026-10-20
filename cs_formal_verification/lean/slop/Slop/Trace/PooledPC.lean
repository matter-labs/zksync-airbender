import Slop.Trace.PooledProgram
import Slop.Trace.PC

namespace Airbender.Trace.Proofs
open Arithmetic

/-- Actual decoder membership gives canonical incoming PCs. Logical state
    matching supplies outgoing bounds; the unresolved terminal condition is
    explicit and is not inferred from the jump family's local constraints. -/
theorem pooled_pc_bounds {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : PooledTrace p} (accepted : Accepted trace) {program : List PooledProgramEntry}
    (decoded : PooledDecoded trace program) (terminal : trace.terminal.word.Bounded) :
    ∀ row ∈ trace.rows, row.start.word.Bounded ∧ row.finish.word.Bounded := by
  have incoming : ∀ row ∈ trace.rows, row.start.word.Bounded := by
    intro row member
    obtain ⟨entry, _, _, query⟩ := decoder_member (decoded row member)
    have canonical := native_query_pc_word hp query
    change row.start.word = Word.ofBitVec entry.pc at canonical
    exact canonical.symm ▸ Word.ofBitVec_bound entry.pc
  have outgoing := outgoing_pc_bounds accepted incoming terminal
  exact fun row member => ⟨incoming row member, outgoing row member⟩

/-- Public instruction addresses are aligned. Their actual decoder queries
    transfer alignment to the native low PC limb without a per-row premise. -/
theorem pooled_pc_alignment {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : PooledTrace p} {program : List PooledProgramEntry}
    (decoded : PooledDecoded trace program)
    (code : ∀ entry ∈ program, entry.pc.toNat % 4 = 0) :
    ∀ row ∈ trace.rows, row.start.word.lo % 4 = 0 := by
  intro row member
  obtain ⟨entry, present, _, query⟩ := decoder_member (decoded row member)
  have canonical := native_query_pc_word hp query
  change row.start.word = Word.ofBitVec entry.pc at canonical
  rw [canonical]
  simpa only [Word.ofBitVec, limbBase, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 65536)]
    using code entry present

end Airbender.Trace.Proofs
