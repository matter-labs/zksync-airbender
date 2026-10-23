import Slop.UnifiedReduced.Claims
import Slop.BabyBear

namespace Tests.UnifiedBinaryImmediate
open Airbender Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private def operation (kind : Fin 6) : ShiftBinop.Operation :=
  if kind.val % 3 = 0 then .xor else if kind.val % 3 = 1 then .or else .and
private def immediate (kind : Fin 6) : BitVec 12 := if kind.val < 3 then 0x678 else 0xdef
private def operand (kind : Fin 6) : BitVec 32 := SailRV32.Functions.sign_extend (m := 32) (immediate kind)
private def rightByte (kind : Fin 6) (i : Nat) : Nat := ((operand kind).extractLsb' (8 * i) 8).toNat
private def outputWord (kind : Fin 6) : BitVec 32 :=
  Verification.byteOperation (operation kind).tag 0xabcd1234 (operand kind)
private def byte (kind : Fin 6) (i : Nat) : Nat := ((outputWord kind).extractLsb' (8 * i) 8).toNat
private def tag (kind : Fin 6) : Nat := UnifiedReduced.Setup.binaryTag (operation kind).tag

private def assignment (kind : Fin 6) : Nat → ZMod babyBearModulus
  | 4 | 5 | 27 | 129 | 130 | 131 | 132 | 133 => 1
  | 7 | 44 => 3
  | 2 | 30 => 4
  | 32 => 8
  | 10 | 92 | 101 | 110 | 119 => (tag kind : ZMod babyBearModulus)
  | 36 => 0x1234 | 37 => 0xabcd
  | 8 | 94 => (rightByte kind 0 : ZMod babyBearModulus)
  | 9 | 89 | 103 => (rightByte kind 1 : ZMod babyBearModulus)
  | 57 | 90 | 112 | 121 => (rightByte kind 2 : ZMod babyBearModulus)
  | 50 => (((outputWord kind).toNat % 65536 : Nat) : ZMod babyBearModulus)
  | 51 => (((outputWord kind).toNat / 65536 : Nat) : ZMod babyBearModulus)
  | 58 | 95 => (byte kind 0 : ZMod babyBearModulus)
  | 62 | 104 => (byte kind 1 : ZMod babyBearModulus)
  | 66 | 113 => (byte kind 2 : ZMod babyBearModulus)
  | 70 | 122 => (byte kind 3 : ZMod babyBearModulus)
  | 74 | 93 => 0x34 | 75 | 111 => 0xcd
  | 102 => 0x12 | 120 => 0xab
  | 88 => 3
  | _ => 0

private def instructionBits (kind : Fin 6) : BitVec 32 :=
  BitVec.ofNat 32 ((immediate kind).toNat * 1048576 +
    if kind.val % 3 = 0 then 0x0c193 else if kind.val % 3 = 1 then 0x0e193 else 0x0f193)
private def before (kind : Fin 6) : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .PC 0 |>.insert .x1 0xabcd1234 |>.insert .x3 0
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 ((instructionBits kind).extractLsb' 0 8)
      |>.insert 1 ((instructionBits kind).extractLsb' 8 8)
      |>.insert 2 ((instructionBits kind).extractLsb' 16 8)
      |>.insert 3 ((instructionBits kind).extractLsb' 24 8) }

private def row (kind : Fin 6) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment kind⟩

private theorem constraints (kind : Fin 6) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment kind)) (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.table (before kind))) := by
  apply Verification.holds_append
  · fin_cases kind
    all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, assignment, outputWord, byte, tag, operation,
      Verification.byteOperation, operand, immediate, rightByte, Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | exact ⟨⟨7, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨254, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨13689, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨4871, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨52737, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨44033, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨13808, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨5118, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨52992, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨44288, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨79225, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨70407, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨118273, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨109569, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨79344, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨70654, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨118528, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨109824, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨144761, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨135943, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨183809, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨175105, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨144880, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨136190, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨184064, by decide⟩, by with_unfolding_all decide⟩
      | exact ⟨⟨175360, by decide⟩, by with_unfolding_all decide⟩
  · fin_cases kind
    all_goals simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

private def trace (kind : Fin 6) : UnifiedTrace babyBearModulus where
  rows := [row kind]
  rom := UnifiedReduced.Setup.table (before kind)
  initial := (row kind).start
  terminal := (row kind).finish
  initialMemory := (row kind).ports.toList.map (readToken (assignment kind))
  terminalMemory := (row kind).ports.toList.map (writeToken (row kind).columns (assignment kind))

private theorem accepted (kind : Fin 6) : Accepted (trace kind) := by
  constructor
  · intro current member
    simp only [trace, List.mem_singleton] at member
    subst current
    exact constraints kind
  · intro current member
    simp only [trace, List.mem_singleton] at member
    subst current
    rfl
  · exact List.Perm.swap _ _ []
  · have exchange : ((row kind).reads ++ (row kind).writes).Perm
        ((row kind).writes ++ (row kind).reads) := List.perm_append_comm
    simpa [trace, Row.reads, Row.writes, row] using exchange

private def cells : List Cell := [.register 1, .register 0, .register 3]
private def entry (kind : Fin 6) : UnifiedReduced.ProgramEntry :=
  ⟨0, instructionBits kind,
    .ITYPE (immediate kind, .Regidx 1, .Regidx 3,
      if kind.val % 3 = 0 then .XORI else if kind.val % 3 = 1 then .ORI else .ANDI),
    ⟨.machine, 1, 0, 3, ShiftBinop.binaryImmediate (operand kind), 65536, tag kind⟩⟩

private theorem public_image (kind : Fin 6) : initialImage (before kind) cells = some (trace kind).initialMemory := by
  have first : (Cell.register 1).read (before kind) = .ok 0xabcd1234 (before kind) := by
    apply read_register; simp [before, Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 0).read (before kind) = .ok 0 (before kind) := rfl
  have third : (Cell.register 3).read (before kind) = .ok 0 (before kind) := by
    apply read_register; simp [before]
  simp only [cells, initialImage, List.mapM_cons, List.mapM_nil, first, second, third]
  fin_cases kind <;> decide

private theorem program_image (kind : Fin 6) : UnifiedReduced.programImage (before kind) [0] = some [entry kind] := by
  have bytes : (Cell.ram 0).read (before kind) = .ok (instructionBits kind) (before kind) := by
    fin_cases kind <;> simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, instructionBits, immediate, Std.ExtHashMap.getElem_insert]
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, bind, Option.bind, pure]
  fin_cases kind <;> with_unfolding_all rfl

private theorem boundary (kind : Fin 6) : ClockBoundary (trace kind) := by
  constructor
  · fin_cases kind <;> constructor <;> decide
  · fin_cases kind <;> decide
  · intro token member
    fin_cases kind
    all_goals simp [trace, row, Row.ports, CircuitLayout.ports, UnifiedReduced.importedConstraintsMemoryPorts] at member
    all_goals rcases member with rfl | rfl | rfl
    all_goals constructor <;> decide

private theorem public_inputs (kind : Fin 6) :
    NativeInputs UnifiedReduced.decoderFields (trace kind) (before kind) cells [entry kind] := by
  constructor
  · decide
  · intro cell member; simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [Cell.Aligned]
  · exact public_image kind
  · refine ⟨⟨4, 0⟩, ?_⟩
    have pc : run (SailRV32.Functions.get_arch_pc ()) (before kind) = .ok 0 (before kind) := by
      apply read_register; simp [before, Std.ExtDHashMap.get?_insert]
    simp only [initialState, pc]
    fin_cases kind <;> rfl
  · exact ⟨[0], program_image kind⟩
  · exact boundary kind

private def input (kind : Fin 6) : ShiftBinop.Input :=
  ⟨operation kind, true, 0xabcd1234, operand kind, ⟨0, 0⟩, .Regidx 1, .Regidx 0, .Regidx 3, immediate kind,
    Trace.retiredState (before kind) 0⟩
private def output (kind : Fin 6) : Output := ⟨Word.ofBitVec (outputWord kind), ⟨4, 0⟩⟩

private theorem decoded (kind : Fin 6) : UnifiedReduced.Decoded (trace kind) [entry kind] := by
  intro current member
  simp only [trace, List.mem_singleton] at member
  subst current
  change ∃ i : Fin 1, _
  exact ⟨0, by fin_cases kind <;> decide⟩

theorem native_soundness (kind : Fin 6) : ShiftBinop.spec (input kind) (output kind) := by
  apply UnifiedReduced.Binary.soundness (by decide) (by decide) (by decide)
    (trace kind) (before kind) cells [entry kind] (input kind) (output kind) (assignment kind)
  refine ⟨⟨public_inputs kind, rfl⟩, ⟨accepted kind, decoded kind, by simp [trace, row]⟩, ?_⟩
  constructor
  · fin_cases kind <;> constructor <;> rfl
  · exact ⟨[], [], before kind, List.Perm.refl _, by simp, WriteHistory.nil _, rfl⟩
  · exact ⟨entry kind, by simp, by fin_cases kind <;> decide, by fin_cases kind <;> rfl⟩

end Tests.UnifiedBinaryImmediate
