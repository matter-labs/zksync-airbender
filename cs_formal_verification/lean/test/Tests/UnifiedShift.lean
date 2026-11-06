import Slop.Sail.ResetState
import Slop.ShiftBinop.Execution
import Slop.UnifiedReduced.Claims
import Slop.UnifiedReduced.Completeness.Shift
import Slop.BabyBear

namespace Tests.UnifiedShift
open Airbender Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

private def operation (kind : Fin 7) : ShiftBinop.Operation :=
  if kind.val = 6 then .rev8 else if kind.val % 3 = 0 then .sll else if kind.val % 3 = 1 then .srl else .sra
private def immediateForm (kind : Fin 7) : Bool := decide (3 ≤ kind.val ∧ kind.val < 6)
private def unusedRight (kind : Fin 7) : Bool := immediateForm kind || kind.val = 6
private def payload (kind : Fin 7) : BitVec 12 := if immediateForm kind then 7 else 0
private def rightWord (kind : Fin 7) : BitVec 32 := if unusedRight kind then 0 else 0x13579b1f
private def amount (kind : Fin 7) : Nat := if kind.val = 6 then 0 else if immediateForm kind then 7 else 31
private def outputWord (kind : Fin 7) : BitVec 32 :=
  Verification.shiftOperation (operation kind).tag 0xabcd1234 (amount kind)
private def rightByte (kind : Fin 7) (i : Nat) : Nat := ((rightWord kind).extractLsb' (8 * i) 8).toNat

private def inputs (kind : Fin 7) : UnifiedReduced.Completeness.Shift :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩, (operation kind).tag, immediateForm kind, (payload kind).toNat, 1,
    if unusedRight kind then 0 else 2, 3, 0x34, 0x12, 0xcd, 0xab,
    rightByte kind 0, rightByte kind 1, rightByte kind 2, rightByte kind 3, 0, 0⟩
private def assignment (kind : Fin 7) : Nat → ZMod babyBearModulus := (inputs kind).honest

private def instructionBits (kind : Fin 7) : BitVec 32 :=
  if kind.val = 0 then 0x002091b3 else if kind.val = 1 then 0x0020d1b3 else if kind.val = 2 then 0x4020d1b3
  else if kind.val = 3 then 0x00709193 else if kind.val = 4 then 0x0070d193 else if kind.val = 5 then 0x4070d193
  else 0x6980d193
private noncomputable def before (kind : Fin 7) : State :=
  { resetMachine with
    regs := resetMachine.regs |>.insert .PC 0 |>.insert .x1 0xabcd1234 |>.insert .x2 0x13579b1f |>.insert .x3 0
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 ((instructionBits kind).extractLsb' 0 8)
      |>.insert 1 ((instructionBits kind).extractLsb' 8 8)
      |>.insert 2 ((instructionBits kind).extractLsb' 16 8)
      |>.insert 3 ((instructionBits kind).extractLsb' 24 8) }

private def row (kind : Fin 7) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment kind⟩

private theorem valid (kind : Fin 7) : (inputs kind).Valid := by
  fin_cases kind <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;>
    decide

private theorem constraints (kind : Fin 7) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment kind)) (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.table (before kind))) :=
  UnifiedReduced.Completeness.Shift.complete _ (valid kind) _

theorem airbender_before (kind : Fin 7) : Configured (before kind) := by
  configured_fixture [before]
private noncomputable def trace (kind : Fin 7) : UnifiedTrace babyBearModulus where
  rows := [row kind]
  rom := UnifiedReduced.Setup.table (before kind)
  initial := (row kind).start
  terminal := (row kind).finish
  initialMemory := (row kind).ports.toList.map (readToken (assignment kind))
  terminalMemory := (row kind).ports.toList.map (writeToken (row kind).columns (assignment kind))

private theorem accepted (kind : Fin 7) : Accepted (trace kind) := by
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

private def cells (kind : Fin 7) : List Cell := [.register 1, .register (if unusedRight kind then 0 else 2), .register 3]
private def entry (kind : Fin 7) : UnifiedReduced.ProgramEntry :=
  ⟨0, instructionBits kind,
    ShiftBinop.Proofs.rowInstruction (operation kind) (immediateForm kind) (payload kind) 1 2 3,
    ⟨.machine, 1, if unusedRight kind then 0 else 2, 3, ⟨(payload kind).toNat, 0⟩, 32768, (operation kind).tag⟩⟩

private theorem public_image (kind : Fin 7) : initialImage (before kind) (cells kind) = some (trace kind).initialMemory := by
  have first : (Cell.register 1).read (before kind) = .ok 0xabcd1234 (before kind) := by
    apply read_register; simp [before, Std.ExtDHashMap.get?_insert]
  have second : (Cell.register (if unusedRight kind then 0 else 2)).read (before kind) = .ok (rightWord kind) (before kind) := by
    fin_cases kind
    all_goals first | rfl | (apply read_register; simp [before, Std.ExtDHashMap.get?_insert, rightWord, unusedRight, immediateForm])
  have third : (Cell.register 3).read (before kind) = .ok 0 (before kind) := by
    apply read_register; simp [before]
  simp only [cells, initialImage, List.mapM_cons, List.mapM_nil, first, second, third]
  fin_cases kind <;> decide

private theorem program_image (kind : Fin 7) : UnifiedReduced.programImage (before kind) [0] = some [entry kind] := by
  have bytes : (Cell.ram 0).read (before kind) = .ok (instructionBits kind) (before kind) := by
    fin_cases kind <;> simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, instructionBits, Std.ExtHashMap.getElem_insert]
  have decoded : decodeOnReset (instructionBits kind) = some (entry kind).instruction := by
    fin_cases kind <;> decode_on_reset
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, decoded, bind, Option.bind, pure]
  fin_cases kind <;> rfl

private theorem boundary (kind : Fin 7) : ClockBoundary (trace kind) := by
  constructor
  · fin_cases kind <;> constructor <;> decide
  · fin_cases kind <;> decide
  · intro token member
    fin_cases kind
    all_goals simp [trace, row, Row.ports, CircuitLayout.ports, UnifiedReduced.importedConstraintsMemoryPorts] at member
    all_goals rcases member with rfl | rfl | rfl
    all_goals constructor <;> decide

private theorem public_inputs (kind : Fin 7) :
    NativeInputs UnifiedReduced.decoderFields (trace kind) (before kind) (cells kind) [entry kind] := by
  constructor
  · fin_cases kind <;> decide
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
  · exact airbender_before kind

private noncomputable def input (kind : Fin 7) : ShiftBinop.Input :=
  ⟨operation kind, immediateForm kind, 0xabcd1234,
    (if immediateForm kind then SailRV32.Functions.sign_extend (m := 32) (payload kind) else rightWord kind),
    ⟨0, 0⟩, .Regidx 1, .Regidx (if unusedRight kind then 0 else 2), .Regidx 3, payload kind,
    Trace.retiredState (before kind) 0⟩
private noncomputable def output (kind : Fin 7) : Output := ⟨Word.ofBitVec (outputWord kind), ⟨4, 0⟩⟩

private theorem decoded (kind : Fin 7) : UnifiedReduced.Decoded (trace kind) [entry kind] := by
  intro current member
  simp only [trace, List.mem_singleton] at member
  subst current
  change ∃ i : Fin 1, _
  exact ⟨0, by fin_cases kind <;> decide⟩

theorem native_soundness (kind : Fin 7) : ShiftBinop.spec (input kind) (output kind) := by
  apply UnifiedReduced.Shift.soundness (by decide) (by decide) (by decide)
    (trace kind) (before kind) (cells kind) [entry kind] (input kind) (output kind) (assignment kind)
  refine ⟨⟨public_inputs kind, rfl⟩, ⟨accepted kind, decoded kind, by simp [trace, row]⟩, ?_⟩
  constructor
  · fin_cases kind <;> constructor <;> with_unfolding_all decide +revert
  · exact ⟨[], [], before kind, List.Perm.refl _, by simp, WriteHistory.nil _, rfl⟩
  · exact ⟨entry kind, by simp, by fin_cases kind <;> decide, by fin_cases kind <;> rfl⟩

end Tests.UnifiedShift
