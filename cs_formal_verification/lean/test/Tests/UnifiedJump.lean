import Slop.UnifiedReduced.Claims
import Slop.BabyBear

namespace Tests.UnifiedJump
open Airbender Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail
open Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

private def assignment (indirect : Bool) : Nat → ZMod babyBearModulus
  | 4 | 7 | 44 | 83 | 88 | 130 | 131 | 132 | 133 => 1
  | 5 => if indirect then 1 else 0
  | 2 | 8 | 50 | 78 | 89 => 4
  | 32 => 8
  | 21 => if indirect then 0 else 1
  | 22 => if indirect then 1 else 0
  | 30 | 122 => if indirect then 12 else 4
  | 36 | 48 => if indirect then 9 else 0
  | 40 => if indirect then 0 else 4
  | 46 => if indirect then 4 else 0
  | 81 | 120 => if indirect then 13 else 4
  | 92 | 101 => 5
  | 110 => 51
  | 119 => 2
  | _ => 0

private def row (indirect : Bool) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment indirect⟩
private def cells : List Cell := [.register 0, .register 1]
private def before (indirect : Bool) : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .PC 0 |>.insert .x1 (if indirect then 9 else 0)
      |>.insert .misa 0x40000100 |>.insert .cur_privilege .Machine |>.insert .mseccfg 0
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 (if indirect then 0xe7 else 0xef) |>.insert 1 (if indirect then 0x80 else 0)
      |>.insert 2 0x40 |>.insert 3 0 }
private def trace (indirect : Bool) : UnifiedTrace babyBearModulus where
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

private theorem constraints (indirect : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment indirect)) (UnifiedReduced.clockConstraints (trace indirect).rom) := by
  apply Verification.holds_append
  · cases indirect <;> simp [UnifiedReduced.importedConstraints, trace,
      FlatOperation.ConstraintsHoldFlat, Verification.environment, Expression.eval, assignment,
      Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | (refine ⟨⟨524549, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨655617, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨786689, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
          UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
      | (refine ⟨⟨721157, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨721166, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
  · cases indirect <;> simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

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
    simp [before, Std.ExtDHashMap.get?_insert]
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, x0, x1, bind, Option.bind]
  cases indirect <;> rfl

private theorem program_image (indirect : Bool) :
    UnifiedReduced.programImage (before indirect) [0] = some [entry indirect] := by
  have bytes : (Cell.ram 0).read (before indirect) = .ok (entry indirect).bits (before indirect) := by
    cases indirect <;> simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, entry, Std.ExtHashMap.getElem_insert]
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, bind, Option.bind, pure]
  cases indirect <;> with_unfolding_all rfl

private theorem inputs (indirect : Bool) :
    NativeInputs UnifiedReduced.decoderFields (trace indirect) (before indirect) cells [entry indirect] := by
  refine ⟨by decide, ?_, public_image indirect, ⟨⟨4, 0⟩, ?_⟩, ⟨[0], program_image indirect⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · have pc : run (SailRV32.Functions.get_arch_pc ()) (before indirect) = .ok 0 (before indirect) := by
      apply read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    simp [initialState, pc, trace, row, Row.start, Row.columns, CircuitLayout.columns,
      UnifiedReduced.importedConstraintsTraceColumns, rawPair, assignment, PCState.boundary, PCState.encode, limbBase]
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

private def input (indirect : Bool) : UnifiedReduced.Jump.Input :=
  ⟨if indirect then .jalr 4 else .jal 4, ⟨if indirect then 9 else 0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩,
    .Regidx 1, .Regidx 1, Trace.retiredState (before indirect) 0⟩
private def output (indirect : Bool) : Output := ⟨⟨4, 0⟩, ⟨if indirect then 12 else 4, 0⟩⟩

theorem sail_jumps (indirect : Bool) : JumpBranchSlt.Jump.spec (input indirect) (output indirect) := by
  apply UnifiedReduced.Jump.soundness (by decide) (by decide) (trace indirect)
    (before indirect) cells [entry indirect] (input indirect) (output indirect) (assignment indirect)
  refine ⟨⟨inputs indirect, rfl, ?_, ?_, ?_⟩,
    ⟨accepted indirect, decoded indirect, by simp [trace, row]⟩, ?_⟩
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    change (0 : Nat) % 4 = 0
    decide
  · exact ⟨0x40000100, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · intro _
    exact ⟨by simp [before, Std.ExtDHashMap.get?_insert], 0,
      by simp [before], rfl⟩
  · constructor
    · cases indirect <;> constructor
      all_goals rfl
    · exact ⟨[], [], before indirect, List.Perm.refl _, by simp, WriteHistory.nil _, rfl⟩
    · exact ⟨entry indirect, by simp, by cases indirect <;> decide, by cases indirect <;> rfl⟩

end Tests.UnifiedJump
