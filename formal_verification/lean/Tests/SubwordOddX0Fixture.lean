import Tests.SubwordOddX0Row
import Airbender.Review.Helpers.Context.SubwordMemory
import Airbender.Proofs.Trace.PublicImage

namespace Tests.SubwordOddX0Fixture
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordOddX0Row
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def entry : SubwordMemory.ProgramEntry :=
  ⟨0,0x00009003,.LOAD (0,.Regidx 1,.Regidx 0,false,2),⟨.lh,1,0,0,⟨0,0⟩,0,1⟩⟩
def cells : List Cell := [.register 1,.ram 4194304,.register 0]

/-- Independent actual public instruction and initialized register/data bytes. -/
def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (4194307 : BitVec 32) |>.insert .PC (0 : BitVec 32))
    mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 4194304 1 |>.insert 4194305 128 |>.insert 4194306 1 |>.insert 4194307 128
      |>.insert 0 3 |>.insert 1 144 |>.insert 2 0 |>.insert 3 0) }

def nativeRow : Row mersenne31Modulus SubwordMemoryFamily := ⟨.subwordMemory,assignment⟩
def seeds : List (MemoryToken mersenne31Modulus) :=
  [(Cell.register 1).initialToken 4194307,(Cell.ram 4194304).initialToken 0x80018001,
    (Cell.register 0).initialToken 0]
def trace : Data mersenne31Modulus SubwordMemoryFamily where
  rows := [nativeRow]
  rom := rom
  initial := ⟨(0,0),(4,0)⟩
  terminal := ⟨(4,0),(8,0)⟩
  initialMemory := seeds
  terminalMemory := nativeRow.writes

theorem accepted : Accepted trace := by
  constructor
  · intro actual present
    have same : actual = nativeRow := by simpa [trace] using present
    subst actual
    exact native_constraints
  · intro actual present
    have same : actual = nativeRow := by simpa [trace] using present
    subst actual
    decide +kernel
  · change [trace.initial,nativeRow.finish].Perm [trace.terminal,nativeRow.start]
    have start : nativeRow.start = trace.initial := rfl
    have finish : nativeRow.finish = trace.terminal := rfl
    rw [start,finish]
    exact List.Perm.swap _ _ []
  · decide +kernel

theorem public_inputs : ImageBoundary trace before cells := by
  have source : (Cell.register 1).read before = .ok (4194307 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have memory : (Cell.ram 4194304).read before = .ok (0x80018001 : BitVec 32) before := by
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,Std.ExtHashMap.getElem_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before = .ok (0 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · decide
  · change initialImage before cells = some seeds
    simp only [initialImage,cells,List.mapM_cons,List.mapM_nil,source,memory]
    rfl
  · rw [initialState,pc]
    rfl

end Tests.SubwordOddX0Fixture
