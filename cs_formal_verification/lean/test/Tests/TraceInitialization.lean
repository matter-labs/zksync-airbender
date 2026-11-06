import Tests.TraceExecution

namespace Tests.TraceInitialization
open Airbender Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private noncomputable def before : State :=
  { Tests.TraceExecution.before with
    regs := Tests.TraceExecution.before.regs.insert .x1 (0 : BitVec 32)
    mem := Tests.TraceExecution.before.mem.insert 4194304 (0 : BitVec 8)
      |>.insert 4194305 0 |>.insert 4194306 0 |>.insert 4194307 0 }

private def cells : List Cell := Tests.TraceExecution.cells ++ [.ram 0, .ram 4194304]
private def tokens : List (MemoryToken babyBearModulus) :=
  Tests.TraceExecution.cells.map (fun cell => cell.initialToken 0) ++
    [Cell.initialToken (.ram 0) 0x00008133, Cell.initialToken (.ram 4194304) 0]
private def trace : Data babyBearModulus where
  rows := []
  rom := ROM.table cells tokens
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 0 (4, 0)
  initialMemory := tokens
  terminalMemory := tokens

private theorem ram : (Cell.ram 4194304).read before = .ok 0 before := by
  simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]

private theorem rom : (Cell.ram 0).read before = .ok 0x00008133 before := by
  simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before,
    Tests.TraceExecution.before, Tests.TraceMemory.sequentialBefore,
    Tests.TraceMemory.publicBefore, Std.ExtHashMap.getElem_insert]

private theorem profile : InitialProfile before cells := by
  constructor
  · apply read_register
    simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  · have numeric : ∀ index : Nat, index < 32 →
        (Cell.register (BitVec.ofNat 5 index)).read before = .ok 0 before := by
      intro index bound
      interval_cases index
      all_goals first
        | rfl
        | (apply read_register; simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert])
    intro index
    simpa using numeric index.toNat index.isLt
  · intro address member bound
    have inTail : address = 0 ∨ address = 4194304 := by
      simpa [cells, Tests.TraceExecution.cells] using member
    rcases inTail with rfl | rfl
    · change 4194304 ≤ 0 at bound
      omega
    · exact ram

/-- Zero GPR/RAM seeds retain the actual nonzero public instruction bytes. -/
theorem canonical_boot_image : bootImage before cells = some trace.initialMemory := by
  simp only [bootImage, cells, Tests.TraceExecution.cells, List.cons_append, List.nil_append,
    List.mapM_cons, List.mapM_nil, rom, show (0 : BitVec 32).toNat < ROM.limit from by decide,
    show ¬(4194304 : BitVec 32).toNat < ROM.limit from by decide, ite_eq_left,
    bind, Option.bind]
  rfl

/-- The fixed profile discharges the existing image, PC and clock boundaries. -/
theorem native_boot_boundary :
    initialImage before cells = some trace.initialMemory ∧
      initialState before (4, 0) = some trace.initial ∧ ClockBoundary trace :=
  Trace.boot_boundary profile canonical_boot_image rfl

/-- The general-state fixture with x1=5 cannot satisfy the boot profile. -/
theorem nonzero_register_rejected :
    ¬InitialProfile Tests.TraceExecution.before Tests.TraceExecution.cells := by
  intro claimed
  have actual : (Cell.register 1).read Tests.TraceExecution.before =
      .ok 5 Tests.TraceExecution.before := by
    apply read_register
    simp [Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  have zero := claimed.registers 1
  rw [actual] at zero
  have impossible : (5 : BitVec 32) = 0 := (EStateM.Result.ok.inj zero).1
  exact (by decide : ¬(5 : BitVec 32) = 0) impossible

/-- A witness cannot change a zero RAM seed while keeping the boot-image check. -/
theorem invented_ram_seed_rejected :
    bootImage before cells ≠ some
      (Tests.TraceExecution.cells.map (fun cell => cell.initialToken (p := babyBearModulus) 0) ++
        [Cell.initialToken (.ram 0) 0x00008133, Cell.initialToken (.ram 4194304) 1]) := by
  rw [canonical_boot_image]
  decide

end Tests.TraceInitialization
