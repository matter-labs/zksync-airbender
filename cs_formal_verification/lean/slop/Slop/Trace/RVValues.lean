import Slop.Trace.PooledValues
import Slop.Trace.RVZero

/-! RV-route twin of `pooled_value_bounds` (`PooledValues.lean`): every native read, write and terminal word of an
    accepted pooled trace is bounded, from the RV public initialization (`initialImageRV`) and the RV program table
    (`rvProgramImageWith pooledDecoderFields`). No Sail state, `Configured` or interpreter fact.

    Changes from the Sail proof: the seed and ROM-table facts read `initialImageRV` (`rvImage_reads`); the two family
    lemmas that took a Sail `Fetched` (jump/branch destination, shift/binop destination) take the projection equation
    `fields` instead, which is all their proofs read. The chronological induction (`read_bounds_of_rules`, ...) is
    state-free and reused. -/

namespace Airbender.Trace.RVValues
open Arithmetic Trace.Proofs

/-- Initial RV tokens carry canonical words. -/
theorem rv_image_bounds {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens) :
    ∀ token ∈ tokens, token.word.Bounded := by
  intro token member
  obtain ⟨cell, _, value, _, rfl⟩ := RVZero.rv_image_token_sources image token member
  rw [initial_token_word]
  exact Word.ofBitVec_bound value

private theorem rv_zip_source {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens)
    {cell : Cell} {token : MemoryToken p} (member : (cell, token) ∈ cells.zip tokens) :
    ∃ bits, cell.readRV before = some bits ∧ token = cell.initialToken bits := by
  have sources := rvImage_reads cells tokens image
  clear image
  induction sources with
  | nil => simp at member
  | @cons first value cells tokens head tail ih =>
    simp only [List.zip_cons_cons, List.mem_cons] at member
    rcases member with equal | member
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact head
    · exact ih member

/-- RV twin of `ROM.Proofs.member`: a word-ROM row is the padding row or a public RAM cell's initial word. -/
theorem rv_rom_member {p : Nat} [Fact p.Prime] {before : RV.State}
    {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (ROM.table cells tokens).Contains #[] query) :
    query = Vector.replicate 9 0 ∨ ∃ address bits, Cell.ram address ∈ cells ∧ address.toNat < ROM.limit ∧
      query = ROM.row address (Word.ofBitVec bits) := by
  obtain ⟨i, equal⟩ := contains
  have present : query ∈ ROM.rows cells tokens := equal ▸ List.get_mem _ i
  simp only [ROM.rows, List.mem_cons, List.mem_filterMap] at present
  rcases present with zero | ⟨⟨cell, token⟩, zipped, mapped⟩
  · exact Or.inl zero
  · obtain ⟨bits, _, source⟩ := rv_zip_source image zipped
    cases cell with
    | register index => simp at mapped
    | ram address =>
      by_cases low : address.toNat < ROM.limit
      · simp only [low, ite_true, Option.some.injEq] at mapped
        right
        refine ⟨address, bits, ?_, low, ?_⟩
        · exact (List.of_mem_zip zipped).1
        · rw [← mapped, source, initial_token_word]
      · simp [low] at mapped

theorem rv_rom_bounds {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {before : RV.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (ROM.table cells tokens).Contains #[] query) :
    query[1].val < limbBase ∧ query[2].val < limbBase := by
  rcases rv_rom_member image contains with rfl | ⟨address, bits, _, _, rfl⟩
  · simp [limbBase]
  · have bound := Word.ofBitVec_bound bits
    change ((Word.ofBitVec bits).lo : ZMod p).val < limbBase ∧
      ((Word.ofBitVec bits).hi : ZMod p).val < limbBase
    rw [ZMod.val_natCast_of_lt (lt_trans bound.1 hp), ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]
    exact bound

theorem rv_rom_disabled {p : Nat} [Fact p.Prime] (hp : 34 < p)
    {before : RV.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (ROM.table cells tokens).Contains #[] query) (inactive : query[8] = 0) :
    query[1] = 0 ∧ query[2] = 0 := by
  rcases rv_rom_member image contains with rfl | ⟨address, bits, _, _, same⟩
  · exact ⟨rfl, rfl⟩
  · rw [same] at inactive
    have tag : (34 : ZMod p) = 0 := inactive
    have value := congrArg ZMod.val tag
    have nonzero : ((34 : Nat) : ZMod p).val = 34 := ZMod.val_natCast_of_lt hp
    norm_num only [Nat.cast_ofNat] at nonzero
    rw [nonzero, ZMod.val_zero] at value
    exact absurd value (by decide)

end Airbender.Trace.RVValues

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace

private theorem rv_decoder_masks {instruction : SailRV32.instruction}
    {data : DecoderData Unit} (fields : decoderFields instruction = some data) :
    data.mask = 1 ∨ data.mask = 2 ∨ data.mask = 4 ∨
      data.mask = 17 ∨ data.mask = 18 ∨ data.mask = 24 := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try (simp only [Option.some.injEq] at fields; subst data)
  all_goals simp_all

private theorem rv_comparison_destination_bounds {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 1 ∧ w 15 = 0) :
    (⟨(w 30).val, (w 31).val⟩ : Word).Bounded := by
  obtain ⟨jal, jalr, comparison, mask⟩ := selected
  have low := Verification.assertion_of_holds h
    ⟨8, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨9, by simp [importedConstraints, FlatOperation.constraints]⟩
  have outputLow := Verification.assertion_of_holds h
    ⟨10, by simp [importedConstraints, FlatOperation.constraints]⟩
  have outputHigh := Verification.assertion_of_holds h
    ⟨11, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, jal, jalr, comparison] at low high
  have lo : w 47 = w 44 := by linear_combination -low
  have hi : w 48 = 0 := high
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mask, lo, hi] at outputLow outputHigh
  have written : w 30 = w 44 := by linear_combination -outputLow
  have resolved := (lookup_values hp h).2.2.1
  rw [show w 31 = 0 by exact outputHigh, written, resolved]
  constructor
  · have bounded (bit : Bool) :
        (((if bit then 1 else 0 : Nat) : ZMod p)).val < limbBase := by
      cases bit <;> simp [limbBase, ZMod.val_one'' (by omega : p ≠ 1)]
    exact bounded _
  · simp [limbBase]

/-- `destination_bounds` with the Sail `Fetched` replaced by the projection equation and the selector facts. -/
theorem rv_destination_bounds {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    {instruction : SailRV32.instruction} {data : DecoderData Unit}
    (fields : decoderFields instruction = some data)
    (flags : ∀ i : Fin 5,
      w importedConstraintsDecoderColumns.flags[i] = if data.mask.testBit i.val then 1 else 0)
    (initialLo : (w 0).val < limbBase) :
    (⟨(w 30).val, (w 31).val⟩ : Word).Bounded := by
  have f0 := flags ⟨0, by decide⟩
  have f1 := flags ⟨1, by decide⟩
  have f2 := flags ⟨2, by decide⟩
  have f3 := flags ⟨3, by decide⟩
  have f4 := flags ⟨4, by decide⟩
  rcases rv_decoder_masks fields with m | m | m | m | m | m
  all_goals simp [importedConstraintsDecoderColumns, m, Nat.testBit] at f0 f1 f2 f3 f4
  · exact (jump_link hp (initial := ⟨(w 0).val, (w 1).val⟩) h
      (by simp [f0, f1]) ⟨f2, f3⟩ ⟨rfl, rfl⟩ initialLo).2
  · exact (jump_link hp (initial := ⟨(w 0).val, (w 1).val⟩) h
      (by simp [f0, f1]) ⟨f2, f3⟩ ⟨rfl, rfl⟩ initialLo).2
  · exact rv_comparison_destination_bounds hp h ⟨f0, f1, f2, f4⟩
  all_goals
    obtain ⟨low, high⟩ := masked_destination h f4
    simp [low, high, Word.Bounded, limbBase]

/-- `row_write_sources` with the Sail `Fetched` replaced by the projection equation and the selector facts. -/
theorem rv_row_write_sources {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (row : Row p TraceKind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) importedConstraints)
    {instruction : SailRV32.instruction} {data : DecoderData Unit}
    (fields : decoderFields instruction = some data)
    (flags : ∀ i : Fin 5, row.assignment importedConstraintsDecoderColumns.flags[i] =
      if data.mask.testBit i.val then 1 else 0)
    (initialLo : (row.assignment 0).val < limbBase) : Trace.Proofs.RowWriteSources row := by
  intro port present
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · left
    simpa [Trace.Proofs.write_word, importedConstraintsMemoryPorts] using
      rv_destination_bounds hp h fields flags initialLo

end Airbender.JumpBranchSlt.Proofs

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace

/-- `row_write_sources` with the Sail `Fetched` replaced by the projection equation and the query. -/
theorem rv_row_write_sources {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    (row : Row p TraceKind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) importedConstraints)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery row.assignment = entry.query) :
    Trace.Proofs.RowWriteSources row := by
  intro port present
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · left
    have flags := decoder_selectors (by dsimp [limbBase]; omega) h
      (decoder_field_bounds fields).2.1 query
    have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
    change row.assignment 10 = (entry.data.funct3 : ZMod p) at tag
    have code : (row.assignment 10).val = entry.data.funct3 := by
      have small := (decoder_field_bounds fields).2.2
      rw [tag, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have destination : (row.assignment 31).val < limbBase ∧
        (row.assignment 32).val < limbBase := by
      rcases decoder_operation_tags fields with ⟨mask, tags⟩ | ⟨mask, tags⟩
      · have selected : row.assignment 11 = 1 ∧ row.assignment 12 = 0 := by
          constructor
          · simpa [importedConstraintsDecoderColumns, mask, Nat.testBit] using flags 0
          · simpa [importedConstraintsDecoderColumns, mask, Nat.testBit] using flags 1
        exact shift_written_bounds hp h selected (code.symm ▸ tags)
      · have selected : row.assignment 11 = 0 ∧ row.assignment 12 = 1 := by
          constructor
          · simpa [importedConstraintsDecoderColumns, mask, Nat.testBit] using flags 0
          · simpa [importedConstraintsDecoderColumns, mask, Nat.testBit] using flags 1
        exact binary_written_bounds (by omega) h selected _ tags tag
    simpa [Trace.Proofs.write_word, importedConstraintsMemoryPorts, Word.Bounded] using destination

end Airbender.ShiftBinop.Proofs

namespace Airbender.Trace.RVValues
open Arithmetic Trace.Proofs

/-- RV twin of `pooled_row_write_rule`: the projection equation replaces `PooledSource`, and the word ROM is built
    from `initialImageRV`. -/
theorem rv_pooled_row_write_rule {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {trace : PooledTrace p} {row : Row p PooledFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints trace.rom))
    (active : row.assignment row.columns.execute = 1)
    {before : RV.State} {cells : List Cell}
    (image : initialImageRV before cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32}
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {entry : PooledProgramEntry} (fields : pooledDecoderFields entry.instruction = some entry.data)
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query) :
    RowWriteBoundsFromReads row := by
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨pc, bits, instruction, data⟩ := entry
  obtain h | h | h | h | h := pooled_fields_cases fields
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      cases mode : d.family
      all_goals simp only [DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
      all_goals subst kind
      all_goals apply row_write_rule_of_sources
      · exact row_write_source ⟨.addSub, w⟩ trace.rom.wordMemory constraints
          (fun query h inactive => rv_rom_disabled (by omega) image
            (by rwa [wordSetup] at h) inactive)
          (fun query h => rv_rom_bounds limbField image (by rwa [wordSetup] at h))
      · exact row_write_source ⟨.wordMemory, w⟩ trace.rom.wordMemory constraints
          (fun query h inactive => rv_rom_disabled (by omega) image
            (by rwa [wordSetup] at h) inactive)
          (fun query h => rv_rom_bounds limbField image (by rwa [wordSetup] at h))
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.jumpBranchSlt = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
      have bounds := JumpBranchSlt.Proofs.decoder_field_bounds fd
      have query' : JumpBranchSlt.decoderQuery w = (⟨pc, bits, instruction, d⟩ : ProgramEntry Unit).query := query
      have flags := JumpBranchSlt.Proofs.decoder_selectors limbField core bounds.2.1 query'
      have pc := native_query_pc_word limbField query
      have low : (w 0).val < limbBase := by
        have bounds := pc.symm ▸ Word.ofBitVec_bound _
        exact bounds.1
      exact row_write_rule_of_sources
        (JumpBranchSlt.Proofs.rv_row_write_sources (by omega) ⟨.jumpBranchSlt, w⟩ core fd flags low)
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.mulDiv = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left MulDiv.importedConstraints MulDiv.importedConstraintsTimestampLookups)
      exact row_write_rule_of_sources (MulDiv.Proofs.row_write_sources ⟨.mulDiv, w⟩ core)
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.shiftBinop = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left ShiftBinop.importedConstraints ShiftBinop.importedConstraintsTimestampLookups)
      exact row_write_rule_of_sources
        (ShiftBinop.Proofs.rv_row_write_sources (entry := ⟨pc, bits, instruction, d⟩) (by omega)
          ⟨.shiftBinop, w⟩ core fd query)
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.subwordMemory = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (SubwordMemory.importedConstraints trace.rom.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      rw [subwordSetup] at core
      exact SubwordMemory.Proofs.row_write_rule hp ⟨.subwordMemory, w⟩ core active

/-- RV twin of `pooled_write_rules`: every row's write rule, from the RV program table. -/
theorem rv_pooled_write_rules {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : rvProgramImageWith pooledDecoderFields initial addresses = some program)
    (decoded : PooledDecoded trace program) : WriteBoundsFromReads trace := by
  intro row member
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  obtain ⟨_, _, _, _, instruction, projection⟩ := rvProgram_entry_fetch programImage entry present
  have fields : pooledDecoderFields entry.instruction = some entry.data := by
    rw [instruction]
    exact projection
  exact rv_pooled_row_write_rule hp (accepted.constraints row member) (accepted.active row member)
    image wordSetup subwordSetup fields family query

/-- RV twin of `pooled_value_bounds`: one RV public image and program table bound every native read, write and
    terminal word. -/
theorem rv_pooled_value_bounds {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : rvProgramImageWith pooledDecoderFields initial addresses = some program)
    (decoded : PooledDecoded trace program) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have rules := rv_pooled_write_rules hp accepted image wordSetup subwordSetup programImage decoded
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have seed := rv_image_bounds image
  exact ⟨read_bounds_of_rules clockField inverse accepted clocks seed rules,
    write_bounds_of_rules clockField inverse accepted clocks seed rules,
    terminal_bounds_of_rules clockField inverse accepted clocks seed rules⟩

end Airbender.Trace.RVValues
