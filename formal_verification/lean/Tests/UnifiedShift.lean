import Airbender.Proofs.ShiftBinop.Execution
import Airbender.Proofs.UnifiedReduced.Claims
import Airbender.Proofs.BabyBear

set_option Elab.async false

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
private def leftByte (i : Nat) : Nat := ((0xabcd1234 : BitVec 32).extractLsb' (8 * i) 8).toNat
private def «part» (kind : Fin 7) (i j : Nat) : Nat :=
  ((Verification.shiftByteContribution i (leftByte i) (amount kind) (operation kind).tag).extractLsb' (8 * j) 8).toNat

private def assignment (kind : Fin 7) : Nat → ZMod babyBearModulus
  | 4 | 5 | 26 | 129 | 130 | 131 | 132 | 133 => 1
  | 6 | 38 => if unusedRight kind then 0 else 2
  | 7 | 44 => 3
  | 2 | 30 => 4
  | 32 => 8
  | 8 => ((payload kind).toNat : ZMod babyBearModulus)
  | 10 => ((operation kind).tag : ZMod babyBearModulus)
  | 36 => 0x1234 | 37 => 0xabcd
  | 42 => (((rightWord kind).toNat % 65536 : Nat) : ZMod babyBearModulus)
  | 43 => (((rightWord kind).toNat / 65536 : Nat) : ZMod babyBearModulus)
  | 50 => (((outputWord kind).toNat % 65536 : Nat) : ZMod babyBearModulus)
  | 51 => (((outputWord kind).toNat / 65536 : Nat) : ZMod babyBearModulus)
  | 57 | 91 => if unusedRight kind then 0 else 31
  | 74 => leftByte 0 | 75 => leftByte 2
  | 76 | 89 => if unusedRight kind then 0 else 0x1f
  | 90 => if unusedRight kind then 0 else 0x9b
  | 88 => 8
  | 80 => 0xabcd1234 * (rightWord kind).toNat * 943718400
  | n => if 58 ≤ n ∧ n < 74 then «part» kind ((n - 58) / 4) ((n - 58) % 4) else
    if 92 ≤ n ∧ n < 128 then
      let i := (n - 92) / 9
      match (n - 92) % 9 with
      | 0 => 9 | 1 => i | 2 => leftByte i | 3 => amount kind
      | 4 => (operation kind).tag | j => «part» kind i (j - 5)
    else 0

private def instructionBits (kind : Fin 7) : BitVec 32 :=
  if kind.val = 0 then 0x002091b3 else if kind.val = 1 then 0x0020d1b3 else if kind.val = 2 then 0x4020d1b3
  else if kind.val = 3 then 0x00709193 else if kind.val = 4 then 0x0070d193 else if kind.val = 5 then 0x4070d193
  else 0x6980d193
private def before (kind : Fin 7) : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .misa 0x40000000 |>.insert .PC 0 |>.insert .x1 0xabcd1234 |>.insert .x2 0x13579b1f |>.insert .x3 0
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 ((instructionBits kind).extractLsb' 0 8)
      |>.insert 1 ((instructionBits kind).extractLsb' 8 8)
      |>.insert 2 ((instructionBits kind).extractLsb' 16 8)
      |>.insert 3 ((instructionBits kind).extractLsb' 24 8) }

private def row (kind : Fin 7) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment kind⟩

private def rowIndex (xs : Vector (ZMod babyBearModulus) 10) : Nat :=
  if xs[9].val = 8 then 196865 + xs[0].val * 256 + xs[1].val else
    262401 + xs[0].val * 65536 + xs[1].val * 256 + xs[2].val * 8 + xs[3].val
private def queryValues (kind : Fin 7) (slot : Fin 5) : Vector (ZMod babyBearModulus) 10 :=
  if slot.val = 0 then #v[assignment kind 89, assignment kind 90, assignment kind 91,
    0, 0, 0, 0, 0, 0, assignment kind 88]
  else let base := 92 + 9 * (slot.val - 1)
    #v[assignment kind (base + 1), assignment kind (base + 2), assignment kind (base + 3),
      assignment kind (base + 4), assignment kind (base + 5), assignment kind (base + 6),
      assignment kind (base + 7), assignment kind (base + 8), 0, assignment kind base]

private theorem checkedRowsFor (initial : State) (kind : Fin 7) (slot : Fin 5) :
    (UnifiedReduced.Setup.table initial).Contains #[] (queryValues kind slot) := by
  change ∃ i : Fin 2097537, _
  have bound : rowIndex (queryValues kind slot) < 1048961 := by
    fin_cases kind <;> fin_cases slot <;> with_unfolding_all decide
  refine ⟨⟨rowIndex (queryValues kind slot), by omega⟩, ?_⟩
  change queryValues kind slot =
    (UnifiedReduced.Setup.row initial ⟨rowIndex (queryValues kind slot), by omega⟩).map
      (fun n : Nat => (n : ZMod babyBearModulus))
  simp only [UnifiedReduced.Setup.row, dif_pos bound]
  rw [UnifiedReduced.Setup.Proofs.fixedRow_eq_reference]
  have binaryBound : rowIndex (queryValues kind slot) < 524545 := by
    fin_cases kind <;> fin_cases slot <;> with_unfolding_all decide
  simp only [UnifiedReduced.Setup.referenceFixedRow, dif_pos binaryBound,
    UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference]
  clear initial
  fin_cases kind <;> fin_cases slot <;> with_unfolding_all decide +revert

private theorem checkedRows (kind : Fin 7) (slot : Fin 5) :
    (UnifiedReduced.Setup.table (before kind)).Contains #[] (queryValues kind slot) :=
  checkedRowsFor (before kind) kind slot

private theorem equations0 (initial : State) :
    ∀ constraint ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints
      (p := babyBearModulus) (UnifiedReduced.Setup.table initial)),
      constraint.eval (Verification.environment (assignment (0 : Fin 7))) = 0 := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, assignment, amount, leftByte, «part», operation, immediateForm,
    unusedRight, payload, rightWord, outputWord, Verification.shiftByteContribution,
    Verification.shiftOperation, ShiftBinop.Operation.tag]; with_unfolding_all decide

private theorem equations1 (initial : State) :
    ∀ constraint ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints
      (p := babyBearModulus) (UnifiedReduced.Setup.table initial)),
      constraint.eval (Verification.environment (assignment (1 : Fin 7))) = 0 := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, assignment, amount, leftByte, «part», operation, immediateForm,
    unusedRight, payload, rightWord, outputWord, Verification.shiftByteContribution,
    Verification.shiftOperation, ShiftBinop.Operation.tag]; with_unfolding_all decide

private theorem equations2 (initial : State) :
    ∀ constraint ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints
      (p := babyBearModulus) (UnifiedReduced.Setup.table initial)),
      constraint.eval (Verification.environment (assignment (2 : Fin 7))) = 0 := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, assignment, amount, leftByte, «part», operation, immediateForm,
    unusedRight, payload, rightWord, outputWord, Verification.shiftByteContribution,
    Verification.shiftOperation, ShiftBinop.Operation.tag]; with_unfolding_all decide

private theorem equations3 (initial : State) :
    ∀ constraint ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints
      (p := babyBearModulus) (UnifiedReduced.Setup.table initial)),
      constraint.eval (Verification.environment (assignment (3 : Fin 7))) = 0 := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, assignment, amount, leftByte, «part», operation, immediateForm,
    unusedRight, payload, rightWord, outputWord, Verification.shiftByteContribution,
    Verification.shiftOperation, ShiftBinop.Operation.tag]; with_unfolding_all decide

private theorem equations4 (initial : State) :
    ∀ constraint ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints
      (p := babyBearModulus) (UnifiedReduced.Setup.table initial)),
      constraint.eval (Verification.environment (assignment (4 : Fin 7))) = 0 := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, assignment, amount, leftByte, «part», operation, immediateForm,
    unusedRight, payload, rightWord, outputWord, Verification.shiftByteContribution,
    Verification.shiftOperation, ShiftBinop.Operation.tag]; with_unfolding_all decide

private theorem equations5 (initial : State) :
    ∀ constraint ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints
      (p := babyBearModulus) (UnifiedReduced.Setup.table initial)),
      constraint.eval (Verification.environment (assignment (5 : Fin 7))) = 0 := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, assignment, amount, leftByte, «part», operation, immediateForm,
    unusedRight, payload, rightWord, outputWord, Verification.shiftByteContribution,
    Verification.shiftOperation, ShiftBinop.Operation.tag]; with_unfolding_all decide

private theorem equations6 (initial : State) :
    ∀ constraint ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints
      (p := babyBearModulus) (UnifiedReduced.Setup.table initial)),
      constraint.eval (Verification.environment (assignment (6 : Fin 7))) = 0 := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, assignment, amount, leftByte, «part», operation, immediateForm,
    unusedRight, payload, rightWord, outputWord, Verification.shiftByteContribution,
    Verification.shiftOperation, ShiftBinop.Operation.tag]; with_unfolding_all decide

private theorem equationsFor (initial : State) (kind : Fin 7) :
    ∀ constraint ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints
      (p := babyBearModulus) (UnifiedReduced.Setup.table initial)),
      constraint.eval (Verification.environment (assignment kind)) = 0 := by
  fin_cases kind
  · exact equations0 initial
  · exact equations1 initial
  · exact equations2 initial
  · exact equations3 initial
  · exact equations4 initial
  · exact equations5 initial
  · exact equations6 initial

private theorem constraintsFor (initial : State) (kind : Fin 7) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment kind)) (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.table initial)) := by
  apply Verification.holds_append
  · apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
    constructor
    · exact equationsFor initial kind
    · intro query member
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
      fin_cases i
      all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.lookups, Lookup.Contains,
        UnifiedReduced.Setup.table,  Table.toRaw, fromElements,
        Expression.eval, Verification.environment]
      all_goals solve
        | (apply Verification.range16_contains; fin_cases kind <;> with_unfolding_all decide)
        | (with_unfolding_all exact checkedRowsFor initial kind 0)
        | (with_unfolding_all exact checkedRowsFor initial kind 1)
        | (with_unfolding_all exact checkedRowsFor initial kind 2)
        | (with_unfolding_all exact checkedRowsFor initial kind 3)
        | (with_unfolding_all exact checkedRowsFor initial kind 4)
  · fin_cases kind
    all_goals simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

private theorem constraints (kind : Fin 7) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment kind))
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.table (before kind))) :=
  constraintsFor (before kind) kind

private def trace (kind : Fin 7) : UnifiedTrace babyBearModulus where
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
  have isa : run (SailRV32.readReg .misa) (before kind) = .ok (0x40000000 : BitVec 32) (before kind) := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have decoded : run (SailRV32.Functions.encdec_backwards (instructionBits kind)) (before kind) =
      .ok (entry kind).instruction (before kind) := by
    fin_cases kind
    all_goals repeat' first
      | (with_unfolding_all rfl)
      | (with_unfolding_all conv_lhs => arg 1; whnf
         rw [@run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
           _ _ SailRV32.Register.misa _ _ _ isa])
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, bind, Option.bind, pure]
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

private def input (kind : Fin 7) : ShiftBinop.Input :=
  ⟨operation kind, immediateForm kind, 0xabcd1234,
    (if immediateForm kind then SailRV32.Functions.sign_extend (m := 32) (payload kind) else rightWord kind),
    ⟨0, 0⟩, .Regidx 1, .Regidx (if unusedRight kind then 0 else 2), .Regidx 3, payload kind,
    Trace.retiredState (before kind) 0⟩
private def output (kind : Fin 7) : Output := ⟨Word.ofBitVec (outputWord kind), ⟨4, 0⟩⟩

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
