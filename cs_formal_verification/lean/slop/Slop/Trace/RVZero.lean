module
public import Slop.Trace.RVHistory
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Helpers.Context.Model
public import Slop.Defs.Helpers.Memory.History

@[expose] public section

/-! RV-route x0 law (piece E0). `zero` for the RV AddSub row (`rv_addsub_row_position`) is derived here, with no Sail
    state or interpreter fact: the initial image is `initialImageRV` (register reads are `RV.State.getReg`), the row
    families are the decoder-projection twins in `RVZeroRows`, and the program entries come from `rvProgramImageWith`
    (`rvProgram_entry_fetch`) with the projection `rvPooledDecoderFields` on `RV.Instr`. The propagation induction is the Sail one (`ZeroValues.lean`) with `initial_zero_value`
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

end Airbender.Trace.RVZero
