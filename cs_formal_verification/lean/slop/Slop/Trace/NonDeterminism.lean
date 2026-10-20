import Human.Trace.NonDeterminism
import Slop.Trace.Program
import Slop.Trace.ZeroRegister

namespace Airbender.Trace.NonDeterminism.Proofs
open Arithmetic

theorem standard_fields {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : Trace.decoderFields instruction = some data) :
    NonDeterminism.decoderFields instruction = some data := by
  unfold NonDeterminism.decoderFields
  split
  · simp [Trace.decoderFields] at fields
  · exact fields

/-- Actual constructor cases admitted by the projection, shared by bounds,
    zero-register preservation and the execution dispatch. -/
theorem fields_cases {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : NonDeterminism.decoderFields instruction = some data) :
    Trace.decoderFields instruction = some data ∨
    (∃ rd : BitVec 5, rd ≠ 0 ∧
      instruction = .CSRReg (0x7C0, .Regidx 0, .Regidx rd, .CSRRW) ∧
      data = ⟨.addSub, 0, 0, rd, ⟨0, 0⟩, 256, 0⟩) ∨
    (∃ rs1 : BitVec 5, rs1 ≠ 0 ∧
      instruction = .CSRReg (0x7C0, .Regidx rs1, .Regidx 0, .CSRRW) ∧
      data = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩) := by
  unfold NonDeterminism.decoderFields at fields
  split at fields
  · rename_i original csr rs1 rd
    change (if csr = 0x7C0 then
      if rs1 = 0 then
        if rd = 0 then none else some ⟨.addSub, 0, 0, rd, ⟨0, 0⟩, 256, 0⟩
      else if rd = 0 then some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ else none
      else none) = some data at fields
    by_cases valid : csr = 0x7C0 <;>
      by_cases source : rs1 = 0 <;>
      by_cases destination : rd = 0 <;> simp_all [Trace.decoderFields]
  · exact Or.inl fields

theorem memory_fields {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : NonDeterminism.decoderFields instruction = some data)
    (family : data.family = .wordMemory) : Trace.decoderFields instruction = some data := by
  rcases fields_cases fields with standard | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact standard
  all_goals cases family

theorem field_bounds {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : NonDeterminism.decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 512 := by
  rcases fields_cases fields with standard | ⟨rd, _, _, rfl⟩ | ⟨rs1, _, _, rfl⟩
  · have bounds := Trace.Proofs.decoder_field_bounds standard
    exact ⟨bounds.1, by omega⟩
  all_goals norm_num [Word.Bounded, limbBase]

theorem zero_nop {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : NonDeterminism.decoderFields instruction = some data)
    (family : data.family = .addSub) (zero : data.rd = 0) :
    data = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by
  rcases fields_cases fields with standard | ⟨rd, nonzero, _, rfl⟩ | ⟨rs1, _, _, rfl⟩
  · exact Trace.Proofs.decoder_zero_nop standard family zero
  · exact False.elim (nonzero zero)
  · rfl

theorem load_nonzero {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : NonDeterminism.decoderFields instruction = some data)
    (family : data.family = .wordMemory) (load : data.mask = 0) : data.rd ≠ 0 := by
  rcases fields_cases fields with standard | ⟨rd, _, _, rfl⟩ | ⟨rs1, _, _, rfl⟩
  · exact Trace.Proofs.decoder_load_nonzero standard family load
  all_goals cases family

/-- The native read tag is fixed by the same packed selector query. -/
theorem read_flag {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} (accepted : Accepted trace) {row : Row p} (member : row ∈ trace.rows)
    {entry : ProgramEntry} (small : entry.data.mask < 512)
    (query : row.decoderQuery = entry.query) :
    isRead row = match row.family with
      | .addSub => entry.data.mask.testBit 8
      | .wordMemory => false := by
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have flags := Trace.Proofs.query_selectors_of_bound hp accepted member small query
      have flag := flags ⟨8, by change 8 < 9; decide⟩
      change w 18 = if entry.data.mask.testBit 8 then 1 else 0 at flag
      simp only [isRead, flag]
      cases entry.data.mask.testBit 8 <;> simp
    | wordMemory => rfl

/-- The same native history proof applies to standard instructions, read
    responses and zero-operand hints. No extra zero-register premise is added. -/
def decoderRules : Trace.Proofs.DecoderRules NonDeterminism.decoderFields where
  bounds _ _ := field_bounds
  zeroNop _ _ := zero_nop
  loadNonzero _ _ := load_nonzero

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
