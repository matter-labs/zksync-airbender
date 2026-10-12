import Airbender.Proofs.UnifiedReduced.Claims
import Airbender.Proofs.BabyBear

namespace Tests.UnifiedComparison
open Airbender Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail
open Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

private def assignment (immediate : Bool) : Nat → ZMod babyBearModulus
  | 4 | 7 | 23 | 44 | 84 | 88 | 130 | 131 | 132 | 133 => 1
  | 2 | 30 | 40 | 81 | 120 | 122 => 4
  | 8 | 9 | 60 | 102 => if immediate then 65535 else 0
  | 10 => 3
  | 32 => 8
  | 50 | 52 | 53 | 59 | 61 | 78 | 89 | 103 | 112 => if immediate then 1 else 0
  | 57 | 90 => if immediate then 0 else 1
  | 92 | 101 => 5
  | 110 => 51
  | 111 => if immediate then 53 else 56
  | 119 => 2
  | _ => 0

private def row (immediate : Bool) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment immediate⟩
private def cells : List Cell := [.register 0, .register 1]
private def before (immediate : Bool) : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .PC 0 |>.insert .misa 0x40000100 |>.insert .x1 0
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 (if immediate then 0x93 else 0xb3) |>.insert 1 0x30
      |>.insert 2 (if immediate then 0xf0 else 0) |>.insert 3 (if immediate then 0xff else 0) }
private def trace (immediate : Bool) : UnifiedTrace babyBearModulus where
  rows := [row immediate]
  rom := UnifiedReduced.Setup.table (before immediate)
  initial := (row immediate).start
  terminal := (row immediate).finish
  initialMemory := cells.map fun cell => cell.initialToken 0
  terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), Nat.pair 0 0⟩,
    ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair (if immediate then 1 else 0) 0⟩]
private def entry (immediate : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, if immediate then 0xfff03093 else 0x000030b3,
    if immediate then .ITYPE (4095, .Regidx 0, .Regidx 1, .SLTIU)
    else .RTYPE (.Regidx 0, .Regidx 0, .Regidx 1, .SLTU),
    ⟨.machine, 0, 0, 1, ⟨if immediate then 65535 else 0, if immediate then 65535 else 0⟩, 4096, 3⟩⟩

private theorem constraints (immediate : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment immediate)) (UnifiedReduced.clockConstraints (trace immediate).rom) := by
  apply Verification.holds_append
  · cases immediate <;> simp [UnifiedReduced.importedConstraints, trace,
      FlatOperation.ConstraintsHoldFlat, Verification.environment, Expression.eval, assignment,
      Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | (refine ⟨⟨524545, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨524546, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨655617, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨786742, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
          UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
      | (refine ⟨⟨786745, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
          UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
      | (refine ⟨⟨721157, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨721152, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
  · cases immediate <;> simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

private theorem accepted (immediate : Bool) : Accepted (trace immediate) := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact constraints immediate
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · cases immediate <;> decide

private theorem public_image (immediate : Bool) :
    initialImage (before immediate) cells = some (trace immediate).initialMemory := by
  have x0 : (Cell.register 0).read (before immediate) = .ok 0 (before immediate) := rfl
  have x1 : (Cell.register 1).read (before immediate) = .ok 0 (before immediate) := by
    apply read_register
    simp [before]
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, x0, x1, bind, Option.bind]
  rfl

private theorem program_image (immediate : Bool) :
    UnifiedReduced.programImage (before immediate) [0] = some [entry immediate] := by
  have bytes : (Cell.ram 0).read (before immediate) = .ok (entry immediate).bits (before immediate) := by
    cases immediate <;> simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, entry, Std.ExtHashMap.getElem_insert]
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, bind, Option.bind, pure]
  cases immediate <;> with_unfolding_all rfl

private theorem inputs (immediate : Bool) :
    NativeInputs UnifiedReduced.decoderFields (trace immediate) (before immediate) cells [entry immediate] := by
  refine ⟨by decide, ?_, public_image immediate, ⟨⟨4, 0⟩, ?_⟩, ⟨[0], program_image immediate⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · have pc : run (SailRV32.Functions.get_arch_pc ()) (before immediate) = .ok 0 (before immediate) := by
      apply read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    simp [initialState, pc, trace, row, Row.start, Row.columns, CircuitLayout.columns,
      UnifiedReduced.importedConstraintsTraceColumns, rawPair, assignment, PCState.boundary, PCState.encode, limbBase]
  · constructor
    · cases immediate <;> constructor <;> decide
    · cases immediate <;> decide
    · intro token member
      cases immediate <;> simp [trace, cells, Cell.initialToken] at member
      all_goals rcases member with rfl | rfl
      all_goals constructor <;> decide

private theorem decoded (immediate : Bool) : UnifiedReduced.Decoded (trace immediate) [entry immediate] := by
  intro current member
  have same := List.mem_singleton.mp member
  subst current
  change ∃ i : Fin 1, _
  exact ⟨0, by cases immediate <;> decide⟩

private def input (immediate : Bool) : UnifiedReduced.Control.Comparison.Input :=
  ⟨if immediate then .sltiu else .sltu, ⟨0, 0⟩,
    ⟨if immediate then 65535 else 0, if immediate then 65535 else 0⟩, ⟨0, 0⟩,
    .Regidx 0, .Regidx 0, .Regidx 1, if immediate then 4095 else 0,
    Trace.retiredState (before immediate) 0⟩
private def output (immediate : Bool) : Output := ⟨⟨if immediate then 1 else 0, 0⟩, ⟨4, 0⟩⟩

theorem sail_comparisons (immediate : Bool) : JumpBranchSlt.Comparison.spec (input immediate) (output immediate) := by
  apply UnifiedReduced.Control.Comparison.soundness (by decide) (by decide) (trace immediate)
    (before immediate) cells [entry immediate] (input immediate) (output immediate) (assignment immediate)
  refine ⟨⟨inputs immediate, rfl, ?_⟩,
    ⟨accepted immediate, decoded immediate, by simp [trace, row]⟩, ?_⟩
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    change (0 : Nat) % 4 = 0
    decide
  · constructor
    · cases immediate <;> constructor
      all_goals rfl
    · exact ⟨[], [], before immediate, List.Perm.refl _, by simp, WriteHistory.nil _, rfl⟩
    · exact ⟨entry immediate, by simp, by cases immediate <;> decide, by cases immediate <;> rfl⟩

end Tests.UnifiedComparison
