module
public import Slop.Trace.RVPooled.AddSub
public import Slop.Trace.RVPooled.WordMemory
public import Slop.Trace.RVPooled.JumpBranchSlt
public import Slop.Trace.RVPooled.MulDiv
public import Slop.Trace.RVPooled.ShiftBinop
public import Slop.Trace.RVPooled.SubwordMemory
public import Slop.Defs.Helpers.Memory.RowEvents
public import Slop.Defs.Helpers.Memory.History

@[expose] public section

/-! Every pooled row with standard metadata takes one `RV.exec` (`rv_pooled_row_step`, by family), and what an accepted
    RV-decoded trace gives for each of its rows (`rv_pooled_row_facts`, for any decoder projection). -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- A pooled row whose metadata is the standard table's (`rvPooledDecoderFields`) takes one `RV.exec`. -/
theorem rv_pooled_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {row : Row p PooledFamily} {before after : RV.State} {entry : RVPooledProgramEntry} {i : RV.Instr}
    (facts : RVPooledRowFacts trace initial cells row before after entry)
    (fields : rvPooledDecoderFields i = some entry.data) (decodes : RV.decode entry.bits = some i) :
    RVPooledRowStep row before after i := by
  obtain ⟨family, w⟩ := row
  cases family
  · obtain ⟨d, fd, dataEq⟩ := (rv_pooled_fields_family fields).1 (Or.inl facts.family)
    exact rv_addsub_row_step hp inverse facts fd dataEq (RV.decode_shape decodes)
  · exact rv_word_row_step hp inverse facts fields decodes
  · exact rv_jbs_row_step hp facts fields decodes
  · exact rv_muldiv_row_step hp inverse facts fields
  · exact rv_shift_row_step hp inverse facts fields (RV.decode_shape decodes)
  · exact rv_subword_row_step hp inverse facts fields decodes

/-- What an accepted trace decoded against a public RV program gives for one of its rows at its RV position, for any
    decoder projection: the row's entry and instruction, `RV.step` = `RV.exec` of it, and the row facts. -/
theorem rv_pooled_row_facts {p : Nat} [Fact p.Prime] (hp : limbBase < p) {trace : PooledTrace p}
    {initial : RV.State} {cells : List Cell} {projection : RV.Instr → Option (DecoderData PooledFamily)}
    {addresses : List (BitVec 32)} {program : List RVPooledProgramEntry}
    (programImage : rvProgramImageWith projection initial addresses = some program)
    (accepted : Accepted trace) (decoded : RVPooledDecoded trace program)
    (bounds : ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded)
    (finishBounds : ∀ row ∈ trace.rows, row.finish.word.Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (wordTable : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    (subwordTable : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial))
    {row : Row p PooledFamily} (member : row ∈ trace.rows) {before after : RV.State}
    (position : RVRowPosition trace initial cells row before)
    (history : RVHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    ∃ entry : RVPooledProgramEntry, ∃ i, RV.decode entry.bits = some i ∧ projection i = some entry.data ∧
      (∀ s : RV.State, s.pc = before.pc → s.rom = before.rom → RV.step s = RV.exec s i) ∧
      RVPooledRowFacts trace initial cells row before after entry := by
  obtain ⟨entry, present, family, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨guard, bits, i, decodes, fields⟩ := rvProgram_entry_fetch programImage entry present
  obtain ⟨beforePC, _⟩ := rv_step_of_position position (rv_query_pc hp query) guard (bits ▸ decodes)
  have rom : before.rom = initial.rom := by
    obtain ⟨_, _, middle, _, _, writes, atState⟩ := position
    rw [atState]
    exact (rvWriteHistory_rom writes : middle.rom = initial.rom)
  have step (s : RV.State) (atPC : s.pc = before.pc) (atROM : s.rom = before.rom) :
      RV.step s = RV.exec s i := by
    have fetched := (rv_step_fetch s initial (atROM.trans rom) entry.pc (atPC.trans beforePC) guard).2
    rw [fetched, ← bits, decodes, Option.bind_some]
  exact ⟨entry, i, decodes, fields, step,
    { constraints := accepted.constraints row member
      active := accepted.active row member
      family := family
      query := query
      pc := beforePC
      pcAligned := guard.2
      readBounds := bounds row member
      finishBound := finishBounds row member
      history := history
      aligned := aligned
      rom := rom
      wordTable := wordTable
      subwordTable := subwordTable }⟩

end Airbender.Trace.Proofs
