import Airbender.Proofs.UnifiedReduced.Claims
import Airbender.Proofs.BabyBear

set_option Elab.async false

namespace Tests.UnifiedBranch
open Airbender Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail
open Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

private def assignment (taken : Bool) : Nat → ZMod babyBearModulus
  | 4 | 24 | 25 | 57 | 85 | 88 | 90 | 130 | 131 | 132 | 133 => 1
  | 2 | 40 => 4
  | 8 | 32 => 8
  | 46 => 5
  | 10 => if taken then 0 else 1
  | 30 | 81 | 120 | 122 => if taken then 8 else 4
  | 59 | 82 | 112 => if taken then 1 else 0
  | 92 | 101 => 5
  | 110 => 51
  | 111 => if taken then 8 else 24
  | 119 => 2
  | _ => 0

private def row (taken : Bool) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment taken⟩
private def cells : List Cell := [.register 0]
private def before (taken : Bool) : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .PC 0 |>.insert .misa 0x40000100
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 0x63 |>.insert 1 (if taken then 4 else 0x14) |>.insert 2 0 |>.insert 3 0 }
private def trace (taken : Bool) : UnifiedTrace babyBearModulus where
  rows := [row taken]
  rom := UnifiedReduced.Setup.table (before taken)
  initial := (row taken).start
  terminal := (row taken).finish
  initialMemory := cells.map fun cell => cell.initialToken 0
  terminalMemory := [⟨(Cell.register 0).addressCode, (6, 0), Nat.pair 0 0⟩]
private def entry (taken : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, if taken then 0x00000463 else 0x00001463,
    .BTYPE (8, .Regidx 0, .Regidx 0, if taken then .BEQ else .BNE),
    ⟨.machine, 0, 0, 0, ⟨8, 0⟩, 24576, if taken then 0 else 1⟩⟩

private theorem constraints (taken : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment taken)) (UnifiedReduced.clockConstraints (trace taken).rom) := by
  apply Verification.holds_append
  · cases taken <;> simp [UnifiedReduced.importedConstraints, trace,
      FlatOperation.ConstraintsHoldFlat, Verification.environment, Expression.eval, assignment,
      Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | (refine ⟨⟨524545, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨655617, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨786697, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
          UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
      | (refine ⟨⟨786713, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
          UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
      | (refine ⟨⟨721157, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
      | (refine ⟨⟨721161, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
  · cases taken <;> simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

private theorem accepted (taken : Bool) : Accepted (trace taken) := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact constraints taken
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · cases taken <;> decide

private theorem public_image (taken : Bool) :
    initialImage (before taken) cells = some (trace taken).initialMemory := by
  have x0 : (Cell.register 0).read (before taken) = .ok 0 (before taken) := rfl
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, x0, bind, Option.bind]
  rfl

private theorem program_image (taken : Bool) :
    UnifiedReduced.programImage (before taken) [0] = some [entry taken] := by
  have bytes : (Cell.ram 0).read (before taken) = .ok (entry taken).bits (before taken) := by
    cases taken <;> simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, entry, Std.ExtHashMap.getElem_insert]
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, bind, Option.bind, pure]
  cases taken <;> with_unfolding_all rfl

private theorem inputs (taken : Bool) :
    NativeInputs UnifiedReduced.decoderFields (trace taken) (before taken) cells [entry taken] := by
  refine ⟨by decide, ?_, public_image taken, ⟨⟨4, 0⟩, ?_⟩, ⟨[0], program_image taken⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    subst cell; trivial
  · have pc : run (SailRV32.Functions.get_arch_pc ()) (before taken) = .ok 0 (before taken) := by
      apply read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    simp [initialState, pc, trace, row, Row.start, Row.columns, CircuitLayout.columns,
      UnifiedReduced.importedConstraintsTraceColumns, rawPair, assignment, PCState.boundary, PCState.encode, limbBase]
  · constructor
    · cases taken <;> constructor <;> decide
    · cases taken <;> decide
    · intro token member
      cases taken <;> simp [trace, cells, Cell.initialToken] at member
      all_goals subst token
      all_goals constructor <;> decide

private theorem decoded (taken : Bool) : UnifiedReduced.Decoded (trace taken) [entry taken] := by
  intro current member
  have same := List.mem_singleton.mp member
  subst current
  change ∃ i : Fin 1, _
  exact ⟨0, by cases taken <;> decide⟩

private def input (taken : Bool) : UnifiedReduced.Control.Branch.Input :=
  ⟨if taken then .BEQ else .BNE, ⟨0, 0⟩, ⟨0, 0⟩, ⟨8, 0⟩, ⟨0, 0⟩,
    .Regidx 0, .Regidx 0, 8, Trace.retiredState (before taken) 0⟩
private def output (taken : Bool) : Output := ⟨⟨0, 0⟩, ⟨if taken then 8 else 4, 0⟩⟩

theorem sail_branches (taken : Bool) : JumpBranchSlt.Branch.spec (input taken) (output taken) := by
  apply UnifiedReduced.Control.Branch.soundness (by decide) (by decide) (trace taken)
    (before taken) cells [entry taken] (input taken) (output taken) (assignment taken)
  refine ⟨⟨⟨inputs taken, rfl, ?_⟩, ?_⟩,
    ⟨accepted taken, decoded taken, by simp [trace, row]⟩, ?_⟩
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    change (0 : Nat) % 4 = 0
    decide
  · exact ⟨0x40000100, by simp [before]⟩
  · constructor
    · cases taken <;> constructor
      all_goals rfl
    · exact ⟨[], [], before taken, List.Perm.refl _, by simp, WriteHistory.nil _, rfl⟩
    · exact ⟨entry taken, by simp, by cases taken <;> decide, by cases taken <;> rfl⟩

end Tests.UnifiedBranch
