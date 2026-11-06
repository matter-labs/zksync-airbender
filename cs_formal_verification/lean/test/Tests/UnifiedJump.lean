import Slop.Sail.ResetState
import Slop.UnifiedReduced.Claims
import Slop.UnifiedReduced.Completeness.Control
import Slop.BabyBear

namespace Tests.UnifiedJump
open Airbender Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail
open Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384

private def witness (indirect : Bool) : UnifiedReduced.Completeness.Control :=
  ⟨⟨0, 0, 4, 0, 0, 0, if indirect then 0 else 4, 0, if indirect then 4 else 0, 0⟩,
    if indirect then 1 else 0, false, 0, if indirect then 1 else 0, 0, 1,
    if indirect then 9 else 0, 0, 0, 0, 4, 0, if indirect then 9 else 0, 0⟩
private def assignment (indirect : Bool) : Nat → ZMod babyBearModulus := (witness indirect).honest

private def row (indirect : Bool) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment indirect⟩
private def cells : List Cell := [.register 0, .register 1]
private noncomputable def before (indirect : Bool) : State :=
  { resetMachine with
    regs := resetMachine.regs |>.insert .PC 0 |>.insert .x1 (if indirect then 9 else 0)
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 (if indirect then 0xe7 else 0xef) |>.insert 1 (if indirect then 0x80 else 0)
      |>.insert 2 0x40 |>.insert 3 0 }
theorem airbender_before (indirect : Bool) : Configured (before indirect) := by
  configured_fixture [before]
private noncomputable def trace (indirect : Bool) : UnifiedTrace babyBearModulus where
  rows := [row indirect]
  rom := UnifiedReduced.Setup.table (before indirect)
  initial := (row indirect).start
  terminal := (row indirect).finish
  initialMemory := cells.map fun cell => cell.initialToken
    (if cell = .register 1 ∧ indirect then 9 else 0)
  terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), Nat.pair 0 0⟩,
    ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 4 0⟩]
private def entry (indirect : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, if indirect then 0x004080e7 else 0x004000ef,
    if indirect then .JALR (4, .Regidx 1, .Regidx 1) else .JAL (4, .Regidx 1),
    ⟨.machine, if indirect then 1 else 0, 0, 1, ⟨4, 0⟩, if indirect then 2048 else 1024, 0⟩⟩

private theorem valid (indirect : Bool) : (witness indirect).Valid := by
  cases indirect <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;>
    decide

private theorem constraints (indirect : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment indirect)) (UnifiedReduced.clockConstraints (trace indirect).rom) :=
  UnifiedReduced.Completeness.Control.complete _ (valid indirect) _

private theorem accepted (indirect : Bool) : Accepted (trace indirect) := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact constraints indirect
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · cases indirect <;> decide

private theorem public_image (indirect : Bool) :
    initialImage (before indirect) cells = some (trace indirect).initialMemory := by
  have x0 : (Cell.register 0).read (before indirect) = .ok 0 (before indirect) := rfl
  have x1 : (Cell.register 1).read (before indirect) = .ok (if indirect then 9 else 0) (before indirect) := by
    apply read_register
    simp [before]
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, x0, x1, bind, Option.bind]
  cases indirect <;> rfl

private theorem program_image (indirect : Bool) :
    UnifiedReduced.programImage (before indirect) [0] = some [entry indirect] := by
  have bytes : (Cell.ram 0).read (before indirect) = .ok (entry indirect).bits (before indirect) := by
    cases indirect <;> simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, entry, Std.ExtHashMap.getElem_insert]
  have decoded : decodeOnReset (entry indirect).bits = some (entry indirect).instruction := by
    cases indirect <;> decode_on_reset
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, decoded, bind, Option.bind, pure]
  cases indirect <;> rfl

private theorem inputs (indirect : Bool) :
    NativeInputs UnifiedReduced.decoderFields (trace indirect) (before indirect) cells [entry indirect] := by
  refine ⟨by decide, ?_, public_image indirect, ⟨⟨4, 0⟩, ?_⟩, ⟨[0], program_image indirect⟩, ?_, airbender_before indirect⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · have pc : run (SailRV32.Functions.get_arch_pc ()) (before indirect) = .ok 0 (before indirect) := by
      apply read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    simp [initialState, pc, trace, row, Row.start, Row.columns, CircuitLayout.columns,
      UnifiedReduced.importedConstraintsTraceColumns, rawPair, assignment, witness, unified_honest,
      PCState.boundary, PCState.encode, limbBase]
  · constructor
    · cases indirect <;> constructor <;> decide
    · cases indirect <;> decide
    · intro token member
      cases indirect <;> simp [trace, cells, Cell.initialToken] at member
      all_goals rcases member with rfl | rfl
      all_goals constructor <;> decide

private theorem decoded (indirect : Bool) : UnifiedReduced.Decoded (trace indirect) [entry indirect] := by
  intro current member
  have same := List.mem_singleton.mp member
  subst current
  change ∃ i : Fin 1, _
  exact ⟨0, by cases indirect <;> decide⟩

private noncomputable def input (indirect : Bool) : UnifiedReduced.Jump.Input :=
  ⟨if indirect then .jalr 4 else .jal 4, ⟨if indirect then 9 else 0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩,
    .Regidx 1, .Regidx 1, Trace.retiredState (before indirect) 0⟩
private noncomputable def output (indirect : Bool) : Output := ⟨⟨4, 0⟩, ⟨if indirect then 12 else 4, 0⟩⟩

theorem sail_jumps (indirect : Bool) : JumpBranchSlt.Jump.spec (input indirect) (output indirect) := by
  apply UnifiedReduced.Jump.soundness (by decide) (by decide) (trace indirect)
    (before indirect) cells [entry indirect] (input indirect) (output indirect) (assignment indirect)
  refine ⟨⟨inputs indirect, rfl, ?_, airbender_before indirect⟩,
    ⟨accepted indirect, decoded indirect, by simp [trace, row]⟩, ?_⟩
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    change (0 : Nat) % 4 = 0
    decide
  · constructor
    · cases indirect <;> constructor
      all_goals rfl
    · exact ⟨[], [], before indirect, List.Perm.refl _, by simp, WriteHistory.nil _, rfl⟩
    · exact ⟨entry indirect, by simp, by cases indirect <;> decide, by cases indirect <;> rfl⟩

end Tests.UnifiedJump
