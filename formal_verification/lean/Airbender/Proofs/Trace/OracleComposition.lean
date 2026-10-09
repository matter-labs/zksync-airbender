import Airbender.Proofs.Trace.OracleExecution
import Airbender.Proofs.Trace.ROMView

namespace Airbender.Trace.NonDeterminism.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace.Proofs

private theorem head_index {p : Nat} [Fact p.Prime] {trace : Data p}
    {row : Row p} {rows : List (Row p)}
    (ordered : (row :: rows).Pairwise (fun a b => b.clock < a.clock))
    (index : readIndex trace row = ((row :: rows).filter fun earlier =>
      isRead earlier && decide (earlier.clock < row.clock)).length) :
    readIndex trace row = (consumed rows).length := by
  rw [index, consumed_length]
  simp only [List.filter_cons, lt_self_iff_false, decide_false,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply List.filter_congr
  intro old member
  simp [(List.pairwise_cons.mp ordered).1 old member]

private theorem remaining_indices {p : Nat} [Fact p.Prime] {trace : Data p}
    {row : Row p} {rows : List (Row p)}
    (ordered : (row :: rows).Pairwise (fun a b => b.clock < a.clock))
    (indices : ∀ current ∈ row :: rows, readIndex trace current =
      ((row :: rows).filter fun earlier => isRead earlier &&
        decide (earlier.clock < current.clock)).length) :
    ∀ current ∈ rows, readIndex trace current =
      (rows.filter fun earlier => isRead earlier && decide (earlier.clock < current.clock)).length := by
  intro current member
  have previous := (List.pairwise_cons.mp ordered).1 current member
  have equal := indices current (List.mem_cons_of_mem row member)
  simpa [List.filter_cons, Nat.not_lt.mpr (Nat.le_of_lt previous)] using equal

set_option backward.isDefEq.respectTransparency false in
theorem row_step {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {program : List ProgramEntry}
    (sources : ∀ entry ∈ program, entry.Source initial NonDeterminism.decoderFields)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (decoded : Decoded trace program) {stream : List (BitVec 32)} (ports : StreamPorts trace stream)
    {row : Row p} (member : row ∈ trace.rows) {position : Nat}
    (index : position = readIndex trace row)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before) :
    NonDeterminism.Step stream program (before, position)
      (retiredState after row.finish.word.toBitVec, position + if isRead row then 1 else 0) := by
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := entry_source_after_history past
    (fun event em current rom address => native_rom_unchanged
      (by dsimp [ROM.limit, timestampBase] at hp ⊢; omega) inverse accepted boundary image
      (native event em) current rom address)
    (sources entry present) (code entry present).1 (code entry present).2
  have effects := instruction_step hp inverse accepted boundary image setup registers aligned ordinary
    configuration initialPC member source.fields family query
    (stream := stream) (position := position)
    (fun read => by rw [index]; exact ports row member read) native past history pc
  have fetched := query_pc (by dsimp [ROM.limit, limbBase] at hp ⊢; omega) query
  rw [fetched] at pc
  exact ⟨entry, present, source, pc, effects⟩

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Compose the same grouped native histories while the reference counter
    advances only on actual decoder-selected external reads. -/
theorem rows_trace {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {program : List ProgramEntry} (sources : ∀ entry ∈ program, entry.Source initial NonDeterminism.decoderFields)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (decoded : Decoded trace program) {stream : List (BitVec 32)} (ports : StreamPorts trace stream)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok trace.initial.word.toBitVec initial)
    (rows : List (Row p))
    (ordered : rows.Pairwise (fun a b => b.clock < a.clock))
    (indices : ∀ current ∈ rows, readIndex trace current =
      (rows.filter fun earlier => isRead earlier && decide (earlier.clock < current.clock)).length)
    (terminal : PCState.State p) {after : State}
    (members : ∀ row ∈ rows, row ∈ trace.rows)
    (native : ∀ event ∈ (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse),
      event ∈ trace.nativeEvents)
    (chain : ((terminal, terminal) :: rows.map (fun row => (row.start, row.finish)) ++
      [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2))
    (history : SailHistory cells
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial after) :
    NonDeterminism.ExecutionTrace stream program (initial, 0)
      ((match rows with
        | [] => after
        | _ :: _ => retiredState after terminal.word.toBitVec), (consumed rows).length) := by
  induction rows generalizing terminal after with
  | nil =>
    cases history
    exact .refl
  | cons row rest ih =>
    have position : (consumed rest).length = readIndex trace row :=
      (head_index ordered (indices row List.mem_cons_self)).symm
    have restIndices := remaining_indices ordered indices
    have restOrdered := (List.pairwise_cons.mp ordered).2
    have count : (consumed (row :: rest)).length =
        (consumed rest).length + if isRead row then 1 else 0 := by
      rw [consumed_length, consumed_length, List.filter_cons]
      cases isRead row <;> simp
    have split : SailHistory cells
        ((rowEvents trace.memoryEpoch row).reverse ++
          rest.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse)) initial after := history
    obtain ⟨middle, past, current⟩ := sail_history_append.mp split
    have linked : terminal = row.finish ∧
        ((row.start, row.start) :: rest.map (fun row => (row.start, row.finish)) ++
          [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2) := by
      cases rest <;> simpa only [List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, List.isChain_cons_cons] using chain
    rcases linked with ⟨rfl, linked⟩
    have restMembers : ∀ old ∈ rest, old ∈ trace.rows :=
      fun old present => members old (List.mem_cons_of_mem row present)
    have restNative : ∀ event ∈ rest.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse),
        event ∈ trace.nativeEvents := fun event present => native event
      (by simpa only [List.flatMap_cons, List.mem_append] using Or.inr present)
    cases rest with
    | nil =>
      have first : row.start = trace.initial := by simpa using linked
      cases past
      have currentPC : run (SailRV32.Functions.get_arch_pc ()) initial =
          .ok row.start.word.toBitVec initial := by rw [first]; exact pc
      have step := row_step hp inverse accepted boundary image setup registers aligned ordinary
        configuration initialPC sources code decoded ports (members row List.mem_cons_self) position
        restNative (.nil initial) current currentPC
      rw [count]
      exact Relation.ReflTransGen.single step
    | cons old rest =>
      have previous := ih restOrdered restIndices row.start restMembers restNative linked past
      let currentPC := row.start.word.toBitVec
      have step := row_step hp inverse accepted boundary
        (retired_state_image image currentPC) setup registers aligned ordinary
        (retired_state_configuration configuration currentPC) initialPC
        (fun entry present => entry_source_retired_state (sources entry present) currentPC)
        code decoded ports (members row List.mem_cons_self) position restNative
        (retired_state_history past currentPC) (retired_state_history current currentPC)
        (retired_state_pc middle currentPC)
      rw [retired_state_overwrite] at step
      rw [count]
      exact previous.tail step

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Full native execution with an independent stream: all standard/read/hint
    rows execute in clock order, reaching the terminal cells and read count. -/
theorem trace_execution {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace initial cells program NonDeterminism.decoderFields)
    (accepted : Accepted trace) (decoded : Decoded trace program)
    {stream : List (BitVec 32)} (ports : StreamPorts trace stream) :
    ∃ after, NonDeterminism.ExecutionTrace stream program (initial, 0) (after, readCount trace) ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (memoryWord sink.value) after := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [ROM.limit, timestampBase] at hp ⊢; omega
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at hp ⊢; omega
  obtain ⟨timestamp, initialBound⟩ := inputs.initialPC
  obtain ⟨addresses, programBound⟩ := inputs.programImage
  have initialPC := initial_pc_bound limbSize initialBound
  have initialRead := initial_state_pc limbSize initialBound
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    decoded_row_history decoderRules clockSize inverse accepted inputs.clocks inputs.image
      inputs.distinct inputs.aligned programBound decoded
  have chain := ordered_row_boundaries clockSize inverse accepted inputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection clockSize inverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have indices : ∀ current ∈ rows, readIndex trace current =
      (rows.filter fun earlier => isRead earlier && decide (earlier.clock < current.clock)).length :=
    fun current _ => (permutation.filter _).length_eq.symm
  have execution := rows_trace hp inverse accepted inputs.clocks inputs.image inputs.rom
    inputs.registers inputs.aligned inputs.ordinary inputs.configuration initialPC
    (program_sources programBound) inputs.code decoded ports initialRead rows ordered indices trace.terminal
    (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  have count : (consumed rows).length = readCount trace :=
    (consumed_length rows).trans (permutation.filter isRead).length_eq
  rw [count] at execution
  let final := match rows with
    | [] => nativeAfter
    | _ :: _ => retiredState nativeAfter trace.terminal.word.toBitVec
  have pc : run (SailRV32.Functions.get_arch_pc ()) final =
      .ok trace.terminal.word.toBitVec final := by
    cases rows with
    | nil =>
      have same : trace.terminal = trace.initial := by simpa using chain
      rw [same]
      exact sail_history_pc_read nativeHistory initialRead
    | cons _ _ => exact retired_state_pc nativeAfter trace.terminal.word.toBitVec
  have realized : SailStateMatches cells history final := by
    cases rows with
    | nil => exact matchedState
    | cons _ _ =>
      exact matches_control
        (matches_control matchedState .nextPC (.inr rfl) trace.terminal.word.toBitVec)
        .PC (.inl rfl) trace.terminal.word.toBitVec
  exact ⟨final, execution, pc, terminal_sail_reads clockSize inverse accepted inputs.clocks
    inputs.image inputs.distinct consistent realized⟩

variable {p : Nat} [Fact p.Prime]

omit [Fact p.Prime] in
@[simp] theorem view_clock (before : State) (native : Row p) :
    (ROMView.row before native).clock = native.clock := by
  change (timeOfPair (ROMView.row before native).start.timestamp).value =
    (timeOfPair native.start.timestamp).value
  rw [ROMView.row_start]

@[simp] theorem view_is_read (before : State) (native : Row p) :
    isRead (ROMView.row before native) = isRead native := by
  rcases native with ⟨family, assignment⟩
  cases family with
  | addSub => rfl
  | wordMemory =>
    dsimp only [ROMView.row]
    split <;> rfl

theorem view_read_index (before : State) (trace : Data p) (native : Row p) :
    readIndex (ROMView.data before trace) (ROMView.row before native) = readIndex trace native := by
  have count : ∀ rows : List (Row p),
      ((rows.map (ROMView.row before)).filter fun earlier => isRead earlier &&
        decide (earlier.clock < (ROMView.row before native).clock)).length =
      (rows.filter fun earlier => isRead earlier && decide (earlier.clock < native.clock)).length := by
    intro rows
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      simp only [view_clock] at ih
      simp only [List.map_cons, List.filter_cons, view_clock, view_is_read]
      split <;> simp [ih]
  exact count trace.rows

/-- The physical ROM view changes no read response or external-stream position. -/
theorem view_stream_ports (before : State) {trace : Data p} {stream : List (BitVec 32)}
    (ports : StreamPorts trace stream) : StreamPorts (ROMView.data before trace) stream := by
  intro lifted member read
  change lifted ∈ trace.rows.map (ROMView.row before) at member
  obtain ⟨native, present, equal⟩ := List.mem_map.mp member
  subst lifted
  rw [view_is_read] at read
  have supplied : stream[readIndex trace native]? = some (response native) := ports native present read
  rw [view_read_index, supplied]
  rcases native with ⟨family, assignment⟩
  cases family with
  | addSub => rfl
  | wordMemory => cases read

theorem view_read_count (before : State) (trace : Data p) :
    readCount (ROMView.data before trace) = readCount trace := by
  have count : ∀ rows : List (Row p),
      ((rows.map (ROMView.row before)).filter isRead).length = (rows.filter isRead).length := by
    intro rows
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      simp only [List.map_cons, List.filter_cons, view_is_read]
      split <;> simp [ih]
  exact count trace.rows

end Airbender.Trace.NonDeterminism.Proofs
