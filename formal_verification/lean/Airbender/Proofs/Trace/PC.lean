import Airbender.Proofs.Trace.DecoderSetup
import Airbender.Proofs.Trace.PublicImage
import Airbender.Proofs.AddSub.PC

namespace Airbender.Trace.Proofs
open Arithmetic

/-- Actual native PC equations apply after public setup derives bounds/alignment.
    The final PC is an RV32 successor, including high-limb rollover. -/
theorem decoded_pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {trace : Data p} {setup : DecoderSetup} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (row : Row p) (member : row ∈ trace.rows) :
    row.finish.word.Bounded ∧ row.finish.word.toBitVec = row.start.word.toBitVec + 4 := by
  have large : limbBase < p := by dsimp [limbBase]; omega
  have bounds := (decoded_word_bounds large image accepted decoded row member).1
  have aligned := decoded_pc_aligned large image accepted decoded row member
  have constraints := accepted.constraints row member
  cases row with
  | mk family w =>
    cases family
    exact AddSub.Proofs.native_pc_successor hp constraints
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ bounds aligned

/-- Public constructors and native matching discharge every PC range/alignment
    input and bound the external terminal PC. No per-row PC premise is supplied. -/
theorem image_pc_soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {trace : Data p} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {count logCapacity : Nat}
    (inputs : ImageBoundary trace before cells)
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, row.start.word.Bounded ∧ row.start.word.lo % 4 = 0 ∧
      row.finish.word.Bounded ∧ row.finish.word.toBitVec = row.start.word.toBitVec + 4) ∧
      trace.terminal.word.Bounded := by
  have large : limbBase < p := by dsimp [limbBase]; omega
  constructor
  · intro row member
    exact ⟨(decoded_word_bounds large image accepted decoded row member).1,
      decoded_pc_aligned large image accepted decoded row member,
      decoded_pc_successor hp image accepted decoded row member⟩
  · have matched := accepted.states.mem_iff.mpr (List.mem_cons_self (l := trace.rows.map Row.start))
    rcases List.mem_cons.mp matched with same | finished
    · rw [same]
      exact initial_pc_bound large inputs.initial
    · obtain ⟨row, member, same⟩ := List.mem_map.mp finished
      rw [← same]
      exact (decoded_pc_successor hp image accepted decoded row member).1

end Airbender.Trace.Proofs
