import Airbender.Proofs.Trace.Arithmetic
import Airbender.Proofs.Trace.WordMemory
import Airbender.Review.Trace.Execution
import Airbender.Proofs.Trace.Terminal
import Mathlib.Data.List.Chain

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

private theorem path_edge_chain {α : Type} {path : List α} {first last : α}
    (head : path.head? = some first) (endPoint : path.getLast? = some last) :
    ((first, first) :: path.zip path.tail ++ [(last, last)]).IsChain
      (fun a b => a.2 = b.1) := by
  induction path generalizing first with
  | nil => simp at head
  | cons a rest ih =>
    have same : a = first := by simpa using head
    subst first
    cases rest with
    | nil =>
      have same : a = last := by simpa using endPoint
      subst last
      simp
    | cons b rest =>
      have tail := ih (first := b) rfl (by simpa using endPoint)
      cases rest with
      | nil => simpa using tail
      | cons c rest =>
        simp only [List.tail_cons, List.zip_cons_cons, List.cons_append,
          List.isChain_cons_cons] at tail ⊢
        exact ⟨trivial, tail⟩

/-- The sorted native rows connect both public endpoints and every adjacent
    instruction boundary. This is derived from the complete state path. -/
theorem ordered_row_boundaries [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {rows : List (Row p)} (permutation : rows.Perm trace.rows)
    (ordered : rows.Pairwise (fun a b => rowClock b < rowClock a)) :
    ((trace.terminal, trace.terminal) ::
      rows.map (fun row => (row.start, row.finish)) ++ [(trace.initial, trace.initial)]).IsChain
      (fun a b => a.1 = b.2) := by
  obtain ⟨path, statePath, edges⟩ :=
    ordered_row_state_path hp inverse accepted boundary permutation ordered
  have chain := path_edge_chain statePath.1 statePath.2.1
  have reversed := List.isChain_reverse.mpr chain
  simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
    List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append, edges] using
    reversed.imp (by intro a b equal; exact equal.symm)

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Discharge every selected original instruction against its native row.
    Decoder fields select the clause; all read/range/effect facts are derived
    by the existing family proofs. No expected instruction effect is assumed. -/
theorem row_instruction_step (profile : ISAProfile) {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {row : Row p} (member : row ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query)
    (loads : profile = .sail → ∀ (imm : BitVec 12) (rs1 : BitVec 5),
      entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4))
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before) :
    ∃ clause, profileClause profile entry.instruction = some clause ∧
      run (normalStep clause) before =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) := by
  have arithmetic (opcode : Opcode) (rs1 rs2 rd : BitVec 5)
      (imm : BitVec 12) (upper : BitVec 20)
      (encoding : entry.instruction = match opcode with
        | .add => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)
        | .addi => .ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)
        | .sub => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB)
        | .lui => .UTYPE (upper, .Regidx rd, .LUI)
        | .auipc => .UTYPE (upper, .Regidx rd, .AUIPC)) :
      ∃ clause, profileClause profile entry.instruction = some clause ∧
        run (normalStep clause) before =
          .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) := by
    have selected : row.family = .addSub := by
      rw [← family]
      have data := fields
      rw [encoding] at data
      cases opcode
      all_goals simp only [decoderFields, Option.some.injEq] at data
      all_goals rw [← data]; unfold arithmeticFields; split <;> rfl
    cases row with
    | mk current w =>
      change current = .addSub at selected
      subst current
      have checked := arithmetic_row_execution hp inverse accepted boundary image setup initialPC
        member fields query opcode rs1 rs2 rd imm upper
        ⟨registers rs1, registers rs2⟩ encoding past history pc
      cases opcode
      all_goals refine ⟨_, ?_, checked⟩
      all_goals cases profile <;> rw [encoding] <;> rfl
  have originalFields := fields
  unfold decoderFields at fields
  split at fields
  case h_1 =>
    rename_i _ rs2 rs1 rd encoding
    exact arithmetic .add rs1 rs2 rd 0 0 encoding
  case h_2 =>
    rename_i _ rs2 rs1 rd encoding
    exact arithmetic .sub rs1 rs2 rd 0 0 encoding
  case h_3 =>
    rename_i _ imm rs1 rd encoding
    exact arithmetic .addi rs1 0 rd imm 0 encoding
  case h_4 =>
    rename_i _ imm rd encoding
    exact arithmetic .lui 0 0 rd 0 imm encoding
  case h_5 =>
    rename_i _ imm rd encoding
    exact arithmetic .auipc 0 0 rd 0 imm encoding
  case h_6 =>
    rename_i _ imm rs1 rd encoding
    change (if (rd : BitVec 5) = 0 then _ else _) = some entry.data at fields
    by_cases zero : (rd : BitVec 5) = 0
    · cases profile with
      | sail => exact False.elim (loads rfl imm rs1 (by simpa only [zero] using encoding))
      | airbender =>
        rw [if_pos zero, Option.some.injEq] at fields
        have selected : row.family = .addSub := by rw [← family, ← fields]; rfl
        cases row with
        | mk current w =>
          change current = .addSub at selected
          subst current
          let nop : ProgramEntry := { entry with instruction := .ITYPE (0, .Regidx 0, .Regidx 0, .ADDI) }
          have nopFields : decoderFields nop.instruction = some nop.data := by
            change some (arithmeticFields 0 0 0 0 1) = some entry.data
            exact congrArg some fields
          have checked := arithmetic_row_execution hp inverse accepted boundary image setup initialPC
            member nopFields (entry := nop) query .addi 0 0 0 0 0
            ⟨registers 0, registers 0⟩ rfl past history pc
          refine ⟨SailRV32.Functions.execute_ITYPE 0 (.Regidx 0) (.Regidx 0) .ADDI, ?_, checked⟩
          rw [encoding, zero]
          rfl
    · have nonzero := zero
      rw [if_neg nonzero, Option.some.injEq] at fields
      have selected : row.family = .wordMemory := by rw [← family, ← fields]
      cases row with
      | mk current w =>
        change current = .wordMemory at selected
        subst current
        refine ⟨SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4, ?_, ?_⟩
        · cases profile with
          | sail => rw [encoding]; rfl
          | airbender =>
            rw [encoding]
            unfold profileClause
            split <;> simp_all [instructionClause]
        · exact word_row_load_step hp inverse accepted boundary image setup aligned ordinary
            configuration initialPC member originalFields (by rw [← fields]) query encoding
            native past history pc
  case h_7 =>
    rename_i _ imm rs2 rs1 encoding
    have data := Option.some.inj fields
    have selected : row.family = .wordMemory := by rw [← family, ← data]
    cases row with
    | mk current w =>
      change current = .wordMemory at selected
      subst current
      refine ⟨SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4, ?_, ?_⟩
      · cases profile <;> rw [encoding] <;> rfl
      · exact word_row_store_step hp inverse accepted boundary image setup aligned ordinary
          configuration initialPC member originalFields query encoding past history pc
  case h_8 => cases fields

/-- Native retirement changes neither code bytes nor the retained pure Sail
    decoder result. This transports existing source evidence, not a new spec. -/
theorem entry_source_retired_state
    {projection : SailRV32.instruction → Option DecoderData} {entry : ProgramEntry} {before : State}
    (source : entry.Source before projection) (pc : BitVec 32) :
    entry.Source (retiredState before pc) projection :=
  ⟨cell_read_PC (.ram entry.pc) (cell_read_nextPC (.ram entry.pc) source.bytes pc) pc,
    source.decoded, source.fields⟩

set_option backward.isDefEq.respectTransparency false in
/-- The current instruction is obtained from logical decoder membership and
    preserved public bytes. Original Sail stepping is supplied by the native
    family proofs, not by a desired-read or desired-result premise. -/
theorem row_execution_step (profile : ISAProfile) {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {program : List ProgramEntry} (sources : ∀ entry ∈ program, entry.Source initial)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (decoded : Decoded trace program) (loads : profile = .sail → NoDiscardedLoads program)
    {row : Row p} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before) :
    Step profile program before (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := entry_source_after_history past
    (fun event em position rom address => native_rom_unchanged
      (by dsimp [ROM.limit, timestampBase] at hp ⊢; omega) inverse accepted boundary image
      (native event em) position rom address)
    (sources entry present) (code entry present).1 (code entry present).2
  have fetched := query_pc (by dsimp [ROM.limit, limbBase] at hp ⊢; omega) query
  have step := row_instruction_step profile hp inverse accepted boundary image setup registers aligned ordinary
    configuration initialPC member source.fields family query (fun original => loads original entry present)
    native past history pc
  rw [fetched] at pc
  exact ⟨entry, present, source, pc, step⟩

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Compose all native rows in their derived order. The first step starts
    from the public state unchanged; subsequent steps reuse the existing
    history through the actual retired Sail control-register states. -/
theorem rows_execution_trace (profile : ISAProfile) {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {program : List ProgramEntry} (sources : ∀ entry ∈ program, entry.Source initial)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (decoded : Decoded trace program) (loads : profile = .sail → NoDiscardedLoads program)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok trace.initial.word.toBitVec initial)
    (rows : List (Row p)) (terminal : PCState.State p) {after : State}
    (members : ∀ row ∈ rows, row ∈ trace.rows)
    (native : ∀ event ∈ (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse),
      event ∈ trace.nativeEvents)
    (chain : ((terminal, terminal) :: rows.map (fun row => (row.start, row.finish)) ++
      [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2))
    (history : SailHistory cells
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial after) :
    ExecutionTrace profile program initial (match rows with
      | [] => after
      | _ :: _ => retiredState after terminal.word.toBitVec) := by
  induction rows generalizing terminal after with
  | nil =>
    cases history
    exact .refl
  | cons row rest ih =>
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
      have step := row_execution_step profile hp inverse accepted boundary image setup registers aligned ordinary
        configuration initialPC sources code decoded loads (members row List.mem_cons_self)
        restNative (.nil initial) current currentPC
      exact Relation.ReflTransGen.single step
    | cons old rest =>
      have previous := ih row.start restMembers restNative linked past
      let currentPC := row.start.word.toBitVec
      have step := row_execution_step profile hp inverse accepted boundary
        (retired_state_image image currentPC) setup registers aligned ordinary
        (retired_state_configuration configuration currentPC) initialPC
        (fun entry present => entry_source_retired_state (sources entry present) currentPC)
        code decoded loads (members row List.mem_cons_self) restNative
        (retired_state_history past currentPC) (retired_state_history current currentPC)
        (retired_state_pc middle currentPC)
      rw [retired_state_overwrite] at step
      exact previous.tail step

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Whole selected-trace soundness, from the public initial state through
    every native instruction row to the actual terminal PC and cell reads. -/
theorem restricted_trace_execution (profile : ISAProfile) {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace initial cells program)
    (loads : profile = .sail → NoDiscardedLoads program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    ∃ after, ExecutionTrace profile program initial after ∧
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
    decoded_row_history standardDecoderRules clockSize inverse accepted inputs.clocks inputs.image
      inputs.distinct inputs.aligned programBound decoded
  have chain := ordered_row_boundaries clockSize inverse accepted inputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection clockSize inverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := rows_execution_trace profile hp inverse accepted inputs.clocks inputs.image inputs.rom
    inputs.registers inputs.aligned inputs.ordinary inputs.configuration initialPC
    (program_sources programBound) inputs.code decoded loads initialRead rows trace.terminal
    (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
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

end Airbender.Trace.Proofs
