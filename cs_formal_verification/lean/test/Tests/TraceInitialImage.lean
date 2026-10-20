import Slop.Trace.InitialImage
import Slop.BabyBear

namespace Tests.TraceInitialImage
open Airbender
open Trace
open Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true

private def before : Reference.RiscV.Sail.State where
  regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x1 (5 : BitVec 32)
  mem := (Std.ExtHashMap.emptyWithCapacity).insert 4194304 (0x78 : BitVec 8)
    |>.insert 4194305 (0x56 : BitVec 8)
    |>.insert 4194306 (0x34 : BitVec 8)
    |>.insert 4194307 (0x12 : BitVec 8)
  tags := ()
  cycleCount := 0
  sailOutput := #[]

private def cells : List Cell := [.register 0, .register 1, .ram 4194304]
private def tokens : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 5,
    Cell.initialToken (.ram 4194304) 0x12345678]

private theorem register_read : Cell.read (.register 1) before = .ok 5 before := by
  apply Reference.RiscV.Sail.read_register
  simp [before]

private theorem memory_read : Cell.read (.ram 4194304) before = .ok 0x12345678 before := by
  simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]

-- Actual Sail GPR reads (including hardwired x0) and byte-order interpretation
-- supply the initial values. No witness or expected-read premise is an input.
theorem extracted : initialImage before cells = some tokens := by
  have zero : Cell.read (.register 0) before = .ok 0 before := rfl
  simp only [initialImage, cells, tokens, List.mapM_cons, List.mapM_nil,
    zero, register_read, memory_read]
  rfl

theorem bounded : ∀ token ∈ tokens, token.word.Bounded := Proofs.image_bounds extracted

theorem unique : (tokens.map MemoryToken.address).Nodup := by
  apply Proofs.image_unique extracted
  decide

-- Extraction must fail instead of inventing defaults for absent public cells.
theorem missing_register : initialImage (p := babyBearModulus) before [.register 2] = none := by
  have absent : Cell.read (.register 2) before = .error _root_.Sail.Error.Unreachable before := by
    have missing : before.regs.get? .x2 = none := by
      simp [before, Std.ExtDHashMap.get?_insert]
    change run (SailRV32.readReg .x2) before = _
    dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects, FreeM.liftM,
      interpretInstructionEffect]
    simp [missing, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.run]
  simp only [initialImage, List.mapM_cons, absent]
  rfl

theorem missing_memory : initialImage (p := babyBearModulus) before [.ram 4194308] = none := by
  have absent : Cell.read (.ram 4194308) before =
      .error (_root_.Sail.Error.OutOfMemoryRange 4194308) before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, EStateM.bind, EStateM.get, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw, before]
  simp only [initialImage, List.mapM_cons, absent]
  rfl

theorem missing_pc : initialState before ((4, 0) : ZMod babyBearModulus × ZMod babyBearModulus) = none := by
  have missing : before.regs.get? .PC = none := by
    simp [before, Std.ExtDHashMap.get?_insert]
  have read : run (SailRV32.Functions.get_arch_pc ()) before =
      .error _root_.Sail.Error.Unreachable before := by
    dsimp [SailRV32.Functions.get_arch_pc, run, SailRV32.readReg, PreSail.readReg,
      interpretSailEffects, FreeM.liftM, interpretInstructionEffect]
    simp [missing, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.run]
  rw [initialState, read]

end Tests.TraceInitialImage
