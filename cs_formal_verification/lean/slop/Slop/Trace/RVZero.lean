import Slop.Trace.RVZeroRows
import Slop.Trace.ZeroValues
import Slop.Trace.PooledProgram
import Slop.Trace.RVHistory
import Slop.Trace.RVFetch

/-! RV-route x0 law (piece E0). `zero` for the RV AddSub row (`rv_addsub_row_position`) is derived here, with no Sail
    state or interpreter fact: the initial image is `initialImageRV` (register reads are `RV.State.getReg`), the row
    families are the decoder-projection twins in `RVZeroRows`, and the program entries come from `rvProgramImageWith`
    (`rvProgram_entry_fetch`). The propagation induction is the Sail one (`ZeroValues.lean`) with `initial_zero_value`
    replaced. -/

namespace Airbender.Trace.RVZero
open Arithmetic Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]

/-- Initial RV tokens: each token comes from a listed cell's `readRV` on the starting state. -/
theorem rv_image_token_sources {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens) :
    ∀ token ∈ tokens, ∃ cell ∈ cells, ∃ value,
      cell.readRV before = some value ∧ token = cell.initialToken value := by
  have reads := rvImage_reads cells tokens image
  clear image
  induction reads with
  | nil => simp
  | @cons cell token cells tokens head tail ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨value, read, same⟩ := head
      exact ⟨cell, List.mem_cons_self, value, read, same⟩
    · obtain ⟨source, sourceMember, value, read, same⟩ := ih actual member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, value, read, same⟩

private theorem rv_initial_zero_value {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) {token : MemoryToken p}
    (member : token ∈ tokens) (address : token.address = (Cell.register 0).addressCode) :
    token.value = 0 := by
  obtain ⟨cell, _, value, read, rfl⟩ := rv_image_token_sources image token member
  have same := cell_address_injective address
  subst cell
  rw [readRV_register] at read
  have value0 := (Option.some.inj read).symm
  subst value0
  have zeroReg : before.getReg 0 = 0 := by simp [RV.State.getReg]
  rw [zeroReg]
  rfl

/-- Public RV initialization and actual prior-write matching root all x0 reads. -/
theorem rv_zero_reads_of_preserving [Fact p.Prime] [ClockLaws Kind p]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p Kind} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : RV.State} {cells : List Cell}
    (image : initialImageRV before cells = some trace.initialMemory)
    (preserves : ZeroPreserving trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      port.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment port).value = 0 := by
  have propagated : ∀ time : Nat, ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (port.event row.columns row.assignment).1 = time →
      port.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment port).value = 0 := by
    intro time
    induction time using Nat.strong_induction_on with
    | h time ih =>
      intro row member port present clock address
      rcases earlier_write hp inverse accepted boundary row member port present with initial | previous
      · exact rv_initial_zero_value image initial address
      · obtain ⟨writer, writerMember, source, sourceMember, same, earlier⟩ := previous
        have sourceZero : source.address.code writer.assignment = (Cell.register 0).addressCode :=
          (congrArg MemoryToken.address same).trans address
        have preserved := preserves writer writerMember source sourceMember sourceZero (by
          intro read readMember order atZero
          apply ih _ (by omega) writer writerMember read readMember rfl atZero)
        exact (congrArg MemoryToken.value same).symm.trans preserved
  intro row member port present
  exact propagated _ row member port present rfl

theorem rv_zero_writes_of_preserving [Fact p.Prime] [ClockLaws Kind p]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p Kind} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : RV.State} {cells : List Cell}
    (image : initialImageRV before cells = some trace.initialMemory)
    (preserves : ZeroPreserving trace) :
    ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 := by
  have reads := rv_zero_reads_of_preserving hp inverse accepted boundary image preserves
  intro event member address
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value, edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp rowEdge
  have present : port ∈ row.ports := by simpa using present
  have zero := preserves row rowMember port present address
    (fun source member _ => reads row rowMember source member)
  change memoryWord (writeToken row.columns row.assignment port).value = 0
  rw [zero]
  rfl

/-- The RV-route pooled row law: the pooled entry's metadata projection is the Sail-free `pooledDecoderFields`
    (the family split is `pooled_fields_cases`), and each family's twin discharges its local x0 law. -/
theorem rv_pooled_row_zero_preserving {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (setup : PooledSetup p) (row : Row p PooledFamily)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup))
    {entry : PooledProgramEntry} (fields : pooledDecoderFields entry.instruction = some entry.data)
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query) :
    RowZeroPreserving row := by
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
      all_goals
        have query' : _ = (⟨pc, bits, instruction, d⟩ : ProgramEntry).query := query
        have mask : d.mask < 512 := by
          have bound := (standardDecoderRules.bounds _ _ fd).2
          omega
      · have fetch : RVFetched (⟨.addSub, w⟩ : Row p) decoderFields :=
          ⟨⟨pc, bits, instruction, d⟩, fd, mode, query',
            row_query_selectors_of_bound limbField setup.wordMemory constraints mask query'⟩
        exact row_zero_write_from_reads standardDecoderRules hp ⟨.addSub, w⟩ setup.wordMemory constraints fetch
      · have fetch : RVFetched (⟨.wordMemory, w⟩ : Row p) decoderFields :=
          ⟨⟨pc, bits, instruction, d⟩, fd, mode, query',
            row_query_selectors_of_bound limbField setup.wordMemory constraints mask query'⟩
        exact row_zero_write_from_reads standardDecoderRules hp ⟨.wordMemory, w⟩ setup.wordMemory constraints fetch
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.jumpBranchSlt = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
      have bounds := JumpBranchSlt.Proofs.decoder_field_bounds fd
      exact jumpBranch_row_zero_preserving limbField ⟨.jumpBranchSlt, w⟩ core
        ⟨pc, bits, instruction, d⟩ fd query
        (JumpBranchSlt.Proofs.decoder_selectors limbField core bounds.2.1 query)
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.mulDiv = kind at family
      subst kind
      exact mulDiv_row_zero_preserving limbField ⟨.mulDiv, w⟩ ⟨pc, bits, instruction, d⟩ fd query
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.shiftBinop = kind at family
      subst kind
      exact shiftBinop_row_zero_preserving limbField ⟨.shiftBinop, w⟩ ⟨pc, bits, instruction, d⟩ fd query
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.subwordMemory = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (SubwordMemory.importedConstraints setup.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      exact subword_row_zero_preserving limbField ⟨.subwordMemory, w⟩ setup.subwordMemory core
        ⟨pc, bits, instruction, d⟩ fd query

/-- Every row of an accepted RV-decoded pooled trace preserves x0, from the public program image alone. -/
theorem rv_pooled_zero_preserving {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {addresses : List (BitVec 32)}
    {program : List PooledProgramEntry}
    (image : rvProgramImageWith pooledDecoderFields initial addresses = some program)
    (decoded : PooledDecoded trace program) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  obtain ⟨_, _, _, _, instruction, projection⟩ := rvProgram_entry_fetch image entry present
  have fields : pooledDecoderFields entry.instruction = some entry.data := by
    rw [instruction]
    exact projection
  exact rv_pooled_row_zero_preserving hp trace.rom row (accepted.constraints row member) fields family query

/-- The `zero` hypothesis of `rv_addsub_row_position`: every native write to x0 carries zero, derived from the RV
    public program and initialization only. -/
theorem rv_pooled_zero_writes {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : rvProgramImageWith pooledDecoderFields initial addresses = some program)
    (decoded : PooledDecoded trace program) :
    ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 :=
  rv_zero_writes_of_preserving hp inverse accepted boundary image
    (rv_pooled_zero_preserving (by dsimp [timestampBase] at hp; omega) accepted programImage decoded)

end Airbender.Trace.RVZero
