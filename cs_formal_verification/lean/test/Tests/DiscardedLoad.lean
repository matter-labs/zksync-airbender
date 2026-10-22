import Tests.TraceExecution
import Tests.TraceZeroRegister

namespace Tests.DiscardedLoad
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- A real LW x0,0(x1), with x1 pointing to aligned ordinary RAM absent from the
-- public sparse byte image. Its native preprocessing records only x0 accesses.
private def before : State :=
  { Tests.TraceExecution.before with
    regs := Tests.TraceExecution.before.regs.insert .x1 (4194304 : BitVec 32)
    mem := Tests.TraceExecution.before.mem.insert 0 (0x03 : BitVec 8) |>.insert 1 0xa0 |>.insert 2 0 |>.insert 3 0 }

private def cells : List Cell := Tests.TraceExecution.cells
private def initial : List (MemoryToken babyBearModulus) :=
  (List.range 32).map fun index =>
    ⟨Nat.pair 0 (Nat.pair index 0), (0, 0), if index = 1 then Nat.pair 0 64 else 0⟩
private def trace : Data babyBearModulus where
  rows := [Tests.TraceZeroRegister.row]
  rom := ROM.table cells initial
  initial := Tests.TraceZeroRegister.row.start
  terminal := Tests.TraceZeroRegister.row.finish
  initialMemory := initial
  terminalMemory := ⟨0, (6, 0), 0⟩ :: initial.drop 1
private def entry : ProgramEntry :=
  ⟨0, 0x0000a003, .LOAD (0, .Regidx 1, .Regidx 0, false, 4),
    ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩

private theorem image : initialImage before cells = some trace.initialMemory := by
  have numeric : ∀ index : Nat, index < 32 →
      (Cell.register (BitVec.ofNat 5 index)).read before =
        .ok (if index = 1 then 4194304 else 0) before := by
    intro index bound
    interval_cases index
    all_goals first
      | rfl
      | (apply read_register; simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert])
  have reads : ∀ index : BitVec 5, (Cell.register index).read before =
      .ok (if index.toNat = 1 then 4194304 else 0) before := by
    intro index
    simpa using numeric index.toNat index.isLt
  simp only [initialImage, cells, Tests.TraceExecution.cells, List.mapM_cons,
    List.mapM_nil, reads, bind, Option.bind]
  rfl

private theorem program_image : programImage before [0] = some [entry] := by
  have bytes : (Cell.ram 0).read before = .ok 0x0000a003 before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  have decoded : SailRV32.Functions.encdec_backwards 0x0000a003 =
      (FreeM.pure (.LOAD (0, .Regidx 1, .Regidx 0, false, 4)) : SailRV32.SailM _) := rfl
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith,
    bytes, decoded, bind, Option.bind]
  rfl

private theorem accepted : Accepted trace := by
  constructor
  · intro row present
    have same := List.mem_singleton.mp present
    subst row
    exact Tests.TraceZeroRegister.local_satisfies
  · intro row present
    have same := List.mem_singleton.mp present
    subst row
    rfl
  · exact List.Perm.swap _ _ []
  · decide

private theorem decoded : Decoded trace [entry] := by
  intro row present
  have same := List.mem_singleton.mp present
  subst row
  change ∃ i : Fin 1, Tests.TraceZeroRegister.row.decoderQuery = _
  exact ⟨0, by decide⟩

private theorem configuration : FlatMemoryConfiguration before := by
  have written : run (SailRV32.Functions.wX_bits (.Regidx 1) 4194304)
      Tests.TraceExecution.before = .ok ()
        { Tests.TraceExecution.before with regs := Tests.TraceExecution.before.regs.insert .x1 4194304 } := by
    simp only [SailRV32.Functions.wX_bits, SailRV32.Functions.wX,
      SailRV32.Functions.regval_into_reg, write_callback_pure]
    exact run_bind_of_ok _ _ _ _ _ (write_register .x1 4194304 Tests.TraceExecution.before)
  have preserved := configuration_gpr_write Tests.TraceExecution.configuration 1 4194304 written
  exact configuration_register_frame
    (before := { Tests.TraceExecution.before with
      regs := Tests.TraceExecution.before.regs.insert .x1 (4194304 : BitVec 32) })
    (after := before) rfl preserved

private theorem inputs : ExecutionBoundary trace before cells [entry] := by
  refine {
    image := image
    initialPC := ⟨(4, 0), ?_⟩
    rom := rfl
    registers := Tests.TraceExecution.inputs.registers
    distinct := Tests.TraceExecution.inputs.distinct
    aligned := Tests.TraceExecution.inputs.aligned
    ordinary := Tests.TraceExecution.inputs.ordinary
    configuration := configuration
    programImage := ⟨[0], program_image⟩
    code := ?_
    clocks := ?_ }
  · intro actual present
    have same := List.mem_singleton.mp present
    subst actual
    decide
  · have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
      apply read_register
      simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
    rw [initialState, pc]
    rfl
  · refine ⟨?_, ?_, Proofs.image_clocks image⟩
    · change 4 < timestampBase ∧ 0 < timestampBase
      constructor <;> decide
    · change 4 % 4 = 0
      decide

/-- Every public boundary condition and native acceptance/membership relation
    holds; only the separately named discarded-load scope restriction fails. -/
theorem native_accepts_discarded_load : ExecutionBoundary trace before cells [entry] ∧
    Accepted trace ∧ Decoded trace [entry] ∧ ¬NoDiscardedLoads [entry] := by
  refine ⟨inputs, accepted, decoded, ?_⟩
  intro scope
  exact scope entry List.mem_cons_self 0 1 rfl

private def prepared : State := { before with regs := before.regs.insert .nextPC (4 : BitVec 32) }

set_option backward.isDefEq.respectTransparency false in
/-- The actual upstream clause still performs the ignored load. Native NOP
    acceptance therefore does not establish its successful Sail execution. -/
theorem original_discarded_load_error  :
    run (normalStep (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx 0) false 4)) before =
      .error (.OutOfMemoryRange 4194304) prepared := by
  have config := configuration_next_pc_write configuration 4
  have source : run (SailRV32.Functions.rX_bits (.Regidx 1)) prepared = .ok 4194304 prepared := by
    apply read_register
    simp [prepared, before, Std.ExtDHashMap.get?_insert]
  have missing : (readBytes (ue := SailRV32.exception) 4 4194304).run prepared =
      .error (.OutOfMemoryRange 4194304) prepared := by
    simp [readBytes, readByte, prepared, before, Tests.TraceExecution.before,
      Tests.TraceMemory.sequentialBefore, Tests.TraceMemory.publicBefore,
      EStateM.run, get, getThe, MonadStateOf.get, bind,
      EStateM.bind, EStateM.get, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw]
  have transfer := virtual_word_read_error config (.Regidx 1) 0 source (by decide)
    (by unfold OrdinaryWordAddress; decide) missing
  have core : run (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx 0) false 4) prepared =
      .error (.OutOfMemoryRange 4194304) prepared := by
    have offset : SailRV32.Functions.sign_extend (m := 32) (0 : BitVec 12) = 0 := by decide
    have width : decide (4 ≤ SailRV32.Functions.xlen_bytes) = true := rfl
    have unitBind {α : Type} (next : Unit → SailRV32.SailM α) :
        ((FreeM.pure () : SailRV32.SailM Unit) >>= next) = next () := rfl
    simp only [SailRV32.Functions.execute_LOAD, offset, width, PreSail.assert, ite_true, unitBind]
    exact run_bind_of_error _ _ _ _ _ transfer
  have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
    apply read_register
    simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  have next := initialize_next_pc pc
  simp only [normalStep]
  rw [run_bind_of_ok _ _ _ _ _ next]
  exact run_bind_of_error _ _ _ _ _ core

/-- This actual public instruction has no successful normal Sail step under
    the otherwise accepted native/public boundary conditions. -/
theorem no_sail_step  (after : State) :
    ¬SailStep [entry] before after := by
  rintro ⟨actual, present, _, _, clause, selected, success⟩
  have same := List.mem_singleton.mp present
  subst actual
  change some (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx 0) false 4) = some clause at selected
  have same := Option.some.inj selected
  subst clause
  rw [original_discarded_load_error] at success
  cases success

/-- In particular, no successful Sail trace can reach the native terminal PC.
    This is a counterexample to dropping the current LW-to-x0 restriction,
    not a claim about the full Airbender system or its admissible public memory. -/
theorem no_native_terminal_execution  :
    ¬∃ after, SailTrace [entry] before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after := by
  rintro ⟨after, execution, pc⟩
  rcases execution.cases_head with same | ⟨middle, step, _⟩
  · subst after
    have actualPC : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
      apply read_register
      simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
    change run (SailRV32.Functions.get_arch_pc ()) before = .ok (4 : BitVec 32) before at pc
    rw [actualPC] at pc
    have impossible : (0 : BitVec 32) = 4 := (EStateM.Result.ok.inj pc).1
    exact (by decide : ¬(0 : BitVec 32) = 4) impossible
  · exact no_sail_step middle step

/-- The documented Airbender deviation covers that exact same accepted trace,
    without supplying an ignored read value or inventing a successful LOAD. -/
theorem profile_terminal_execution  :
    ∃ after, AirbenderTrace [entry] before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (memoryWord sink.value) after :=
  Trace.airbender_soundness inputs accepted decoded

end Tests.DiscardedLoad
