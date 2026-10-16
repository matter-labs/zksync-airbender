import Airbender.Proofs.UnifiedReduced.Claims

set_option Elab.async false

namespace Tests.UnifiedMemory
open Airbender Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

private def zeroSetup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
  name := "UnifiedRamDisabledQueries"
  length := 1
  row _ := Vector.replicate 10 0
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => Vector.replicate 10 0) i
  contains_iff _ := Iff.rfl
}

private def assignment (store : Bool) : Nat → ZMod babyBearModulus
  | 4 | 5 | 129 | 130 | 131 | 132 | 133 => 1
  | 6 => if store then 2 else 0
  | 7 => if store then 0 else 2
  | 28 => if store then 0 else 1
  | 29 => if store then 1 else 0
  | 2 | 30 => 4
  | 32 => 8
  | 37 | 58 => 64
  | 38 => if store then 2 else 0
  | 39 => if store then 0 else 64
  | 44 => if store then 0 else 2
  | 45 => if store then 64 else 0
  | 42 | 50 => 0x1234
  | 43 | 51 => 0xbeef
  | 80 => 4194304 * (0x1234 + 65536 * 0xbeef) * 943718400
  | _ => 0

private def row (store : Bool) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment store⟩

private theorem constraints (store : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment store)) (UnifiedReduced.clockConstraints zeroSetup) := by
  apply Verification.holds_append
  · cases store <;>
      simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
        Verification.environment, Expression.eval, assignment, Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | (exact ⟨⟨0, by decide⟩, rfl⟩)
  · cases store <;>
      simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

private def trace (store : Bool) : UnifiedTrace babyBearModulus where
  rows := [row store]
  rom := zeroSetup
  initial := (row store).start
  terminal := (row store).finish
  initialMemory := (row store).ports.toList.map (readToken (assignment store))
  terminalMemory := (row store).ports.toList.map (writeToken (row store).columns (assignment store))

private theorem accepted (store : Bool) : Accepted (trace store) := by
  constructor
  · intro current member
    simp only [trace, List.mem_singleton] at member
    subst current
    exact constraints store
  · intro current member
    simp only [trace, List.mem_singleton] at member
    subst current
    rfl
  · exact List.Perm.swap _ _ []
  · have exchange : ((row store).reads ++ (row store).writes).Perm
        ((row store).writes ++ (row store).reads) := List.perm_append_comm
    simpa [trace, Row.reads, Row.writes, row] using exchange

private def cells (store : Bool) : List Cell :=
  [.register 1, if store then .register 2 else .ram 4194304,
    if store then .ram 4194304 else .register 2]

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

private def before (store : Bool) : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0) |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [rv32Region attributes] |>.insert .mhartid 7 |>.insert .htif_tohost_base none
      |>.insert .PC 0 |>.insert .x1 4194304 |>.insert .x2 (if store then 0xbeef1234 else 0)
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 4194304 (if store then 0 else 0x34) |>.insert 4194305 (if store then 0 else 0x12)
      |>.insert 4194306 (if store then 0 else 0xef) |>.insert 4194307 (if store then 0 else 0xbe)
      |>.insert 0 (if store then 0x23 else 0x03) |>.insert 1 (if store then 0xa0 else 0xa1)
      |>.insert 2 (if store then 0x20 else 0) |>.insert 3 0 }


private def entry (store : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, if store then 0x0020a023 else 0x0000a103,
    if store then .STORE (0, .Regidx 2, .Regidx 1, 4) else .LOAD (0, .Regidx 1, .Regidx 2, false, 4),
    ⟨.machine, 1, if store then 2 else 0, if store then 0 else 2, ⟨0, 0⟩,
      if store then 262144 else 131072, 0⟩⟩

private theorem program_image (store : Bool) :
    UnifiedReduced.programImage (before store) [0] = some [entry store] := by
  have bytes : (Cell.ram 0).read (before store) = .ok (entry store).bits (before store) := by
    cases store <;> simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, entry, Std.ExtHashMap.getElem_insert]
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, bind, Option.bind, pure]
  cases store <;> with_unfolding_all rfl

private theorem public_image (store : Bool) :
    initialImage (before store) (cells store) = some (trace store).initialMemory := by
  have first : (Cell.register 1).read (before store) = .ok 4194304 (before store) := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 2).read (before store) =
      .ok (if store then 0xbeef1234 else 0) (before store) := by
    apply read_register
    simp [before]
  have bytes : (Cell.ram 4194304).read (before store) =
      .ok (if store then 0 else 0xbeef1234) (before store) := by
    cases store <;> simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  cases store
  all_goals simp only [cells, Bool.false_eq_true, if_false, if_true, initialImage,
    List.mapM_cons, List.mapM_nil, first, second, bytes]
  all_goals decide

private theorem boundary (store : Bool) : ClockBoundary (trace store) := by
  constructor
  · cases store <;> constructor <;> decide
  · cases store <;> decide
  · intro token member
    cases store <;>
      simp [trace, row, Row.ports, CircuitLayout.ports,
        UnifiedReduced.importedConstraintsMemoryPorts] at member
    all_goals rcases member with rfl | rfl | rfl
    all_goals constructor <;> decide

private theorem public_inputs (store : Bool) :
    NativeInputs UnifiedReduced.decoderFields (trace store) (before store) (cells store) [entry store] := by
  constructor
  · cases store <;> decide
  · intro cell member
    cases store <;> simp only [cells, Bool.false_eq_true, if_false, if_true,
      List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals rcases member with rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  · exact public_image store
  · refine ⟨⟨4, 0⟩, ?_⟩
    have pc : run (SailRV32.Functions.get_arch_pc ()) (before store) = .ok 0 (before store) := by
      apply read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    simp only [initialState, pc]
    cases store <;> rfl
  · exact ⟨[0], program_image store⟩
  · exact boundary store

set_option backward.isDefEq.respectTransparency false in
private theorem configuration (store : Bool) : FlatMemoryConfiguration (before store) := by
  constructor
  · simp [before, Std.ExtDHashMap.get?_insert]
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨0x40000100, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0x10, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨Vector.replicate 64 0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨attributes, by simp [before, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩
  · exact ⟨7, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, Std.ExtDHashMap.get?_insert]

private def input (store : Bool) : Airbender.WordMemory.Input :=
  ⟨store, ⟨0, 64⟩, ⟨0, 0⟩, ⟨0x1234, 0xbeef⟩, ⟨0, 0⟩,
    .Regidx 1, .Regidx 2, if store then .Regidx 0 else .Regidx 2, 0, Trace.retiredState (before store) 0⟩
private def output : Airbender.WordMemory.Output := ⟨⟨0, 64⟩, ⟨0x1234, 0xbeef⟩, ⟨4, 0⟩⟩

private theorem decoded (store : Bool) : UnifiedReduced.Decoded (trace store) [entry store] := by
  intro current member
  simp only [trace, List.mem_singleton] at member
  subst current
  change ∃ i : Fin 1, _
  exact ⟨0, by cases store <;> decide⟩

theorem ram_soundness [Sail.ArchSem.MemoryPlatform SailRV32.exception] (store : Bool) : Airbender.WordMemory.spec (input store) output := by
  apply UnifiedReduced.WordMemory.soundness (by decide) (by decide) (trace store) (before store)
    (cells store) [entry store] (input store) output (assignment store)
  refine ⟨?_, ⟨accepted store, decoded store, by simp [trace, row]⟩, ?_⟩
  · constructor
    · exact public_inputs store
    · exact configuration store
    · intro address member
      cases store <;> simp [cells] at member
      all_goals subst address
      all_goals unfold OrdinaryWordAddress
      all_goals decide
    · intro address member
      cases store <;> simp [cells] at member
      all_goals subst address
      all_goals decide
    · cases store <;> simp [input, zeroRegister]
  · constructor
    · cases store <;> constructor
      all_goals rfl
    · exact ⟨[], [], before store, List.Perm.refl _, by simp, WriteHistory.nil _, rfl⟩
    · exact ⟨entry store, by simp, by cases store <;> decide, by cases store <;> rfl⟩

end Tests.UnifiedMemory
