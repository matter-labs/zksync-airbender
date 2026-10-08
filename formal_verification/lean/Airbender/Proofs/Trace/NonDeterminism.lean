import Airbender.Review.Trace.NonDeterminism
import Airbender.Proofs.Trace.Program

namespace Airbender.Trace.NonDeterminism.Proofs
open Arithmetic

theorem field_bounds {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : NonDeterminism.decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 512 := by
  unfold NonDeterminism.decoderFields at fields
  split at fields
  · rename_i original csr rs1 rd
    change (if csr = 0x7C0 then
      if rs1 = 0 then
        if rd = 0 then none else some ⟨.addSub, 0, 0, rd, ⟨0, 0⟩, 256⟩
      else if rd = 0 then some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1⟩ else none
      else none) = some data at fields
    by_cases valid : csr = 0x7C0 <;>
      by_cases source : rs1 = 0 <;>
      by_cases destination : rd = 0 <;>
      simp_all [Word.Bounded, limbBase]
    all_goals obtain ⟨_, rfl⟩ := fields
    all_goals norm_num
  · have bounds := Trace.Proofs.decoder_field_bounds fields
    exact ⟨bounds.1, by omega⟩

/-- Fetch, actual Sail decoding, all native indices/immediates and the nine
    Boolean selector bits are checked with the same shared decoder machinery. -/
theorem decoder_soundness {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} (accepted : Accepted trace) {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImageWith NonDeterminism.decoderFields before addresses = some program)
    (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.Fetched before NonDeterminism.decoderFields :=
  Trace.Proofs.decoder_soundness_with hp (fun _ _ h => (field_bounds h).2) accepted image decoded

end Airbender.Trace.NonDeterminism.Proofs
