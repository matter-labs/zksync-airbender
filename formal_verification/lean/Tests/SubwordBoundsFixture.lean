import Tests.SubwordBoundsRows

namespace Tests.SubwordBoundsFixture
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordBoundsRows Tests.SubwordBoundsWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def store (sample : Fin 8) : Bool := sample.val = 4 ∨ sample.val = 5
def discarded (sample : Fin 8) : Bool := sample.val = 3
def aliasing (sample : Fin 8) : Bool := sample.val = 7
def address (sample : Fin 8) : BitVec 32 :=
  if sample.val = 1 then 4 else if 2 ≤ sample.val ∧ sample.val ≤ 5 then 4194304 else 0
def sourceValue (sample : Fin 8) : BitVec 32 :=
  if sample.val = 1 then 6 else if sample.val = 2 then 4194305
  else if sample.val = 3 then 4194306 else if sample.val = 4 then 4194307
  else if sample.val = 5 then 4194304 else 0
def entry (sample : Fin 8) : SubwordMemory.ProgramEntry :=
  if sample.val = 7 then
    ⟨0,0x00008083,.LOAD (0,.Regidx 1,.Regidx 1,false,1),⟨.lb,1,0,1,⟨0,0⟩,0,0⟩⟩
  else Tests.SubwordDecoderFixture.entry ⟨sample.val % 7,Nat.mod_lt _ (by decide)⟩
def memoryValue (sample : Fin 8) : BitVec 32 :=
  if sample.val = 0 ∨ sample.val = 6 ∨ sample.val = 7 then (entry sample).bits
  else if store sample then 0x89cd4567 else 0x80018001
def operand (sample : Fin 8) : Cell :=
  if store sample then .register 2 else .ram (address sample)
def target (sample : Fin 8) : Cell :=
  if store sample then .ram (address sample)
  else .register (if discarded sample then 0 else if aliasing sample then 1 else 3)
def cells (sample : Fin 8) : List Cell :=
  if aliasing sample then [.register 1,operand sample]
  else [.register 1,operand sample,target sample]

/-- One independent public state supplies original instruction bytes and all
    initialized register/RAM values, including actual code bytes in shadow cells.
    Correspondence to architectural data-ROM lookup contents remains separate. -/
def before (sample : Fin 8) : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (sourceValue sample) |>.insert .x2 (0xdead12ab : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32))
    mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert (address sample).toNat (BitVec.ofNat 8 (memoryValue sample).toNat)
      |>.insert ((address sample).toNat + 1) (BitVec.ofNat 8 ((memoryValue sample).toNat / 256))
      |>.insert ((address sample).toNat + 2) (BitVec.ofNat 8 ((memoryValue sample).toNat / 65536))
      |>.insert ((address sample).toNat + 3) (BitVec.ofNat 8 ((memoryValue sample).toNat / 16777216))
      |>.insert 0 (BitVec.ofNat 8 (entry sample).bits.toNat)
      |>.insert 1 (BitVec.ofNat 8 ((entry sample).bits.toNat / 256))
      |>.insert 2 (BitVec.ofNat 8 ((entry sample).bits.toNat / 65536))
      |>.insert 3 (BitVec.ofNat 8 ((entry sample).bits.toNat / 16777216))) }

def nativeRow (sample : Fin 8) : Row mersenne31Modulus SubwordMemoryFamily :=
  ⟨.subwordMemory,assignment sample⟩

def seeds (sample : Fin 8) : List (MemoryToken mersenne31Modulus) :=
  let first := (Cell.register 1).initialToken (sourceValue sample)
  let second := (operand sample).initialToken (if store sample then 0xdead12ab else memoryValue sample)
  if aliasing sample then [first,second]
  else [first,second,(target sample).initialToken (if store sample then memoryValue sample else 0)]

def trace (sample : Fin 8) : Data mersenne31Modulus SubwordMemoryFamily where
  rows := [nativeRow sample]
  rom := rom
  initial := ⟨(0,0),(4,0)⟩
  terminal := ⟨(4,0),(8,0)⟩
  initialMemory := seeds sample
  terminalMemory := if aliasing sample then
    [writeToken (nativeRow sample).columns (assignment sample) importedConstraintsMemoryPorts[1],
     writeToken (nativeRow sample).columns (assignment sample) importedConstraintsMemoryPorts[2]]
    else (nativeRow sample).writes

theorem accepted (sample : Fin 8) : Accepted (trace sample) := by
  constructor
  · intro actual member
    have same : actual = nativeRow sample := by simpa [trace] using member
    subst actual
    exact native_constraints sample
  · intro actual member
    have same : actual = nativeRow sample := by simpa [trace] using member
    subst actual
    fin_cases sample <;> decide +kernel
  · change [(trace sample).initial,(nativeRow sample).finish].Perm
      [(trace sample).terminal,(nativeRow sample).start]
    have start : (nativeRow sample).start = (trace sample).initial := by fin_cases sample <;> rfl
    have finish : (nativeRow sample).finish = (trace sample).terminal := by fin_cases sample <;> rfl
    rw [start,finish]
    exact List.Perm.swap _ _ []
  · fin_cases sample <;> decide +kernel

theorem public_inputs (sample : Fin 8) : ImageBoundary (trace sample) (before sample) (cells sample) := by
  have first : (Cell.register 1).read (before sample) = .ok (sourceValue sample) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have memory : (Cell.ram (address sample)).read (before sample) = .ok (memoryValue sample) (before sample) := by
    fin_cases sample <;>
      simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
        EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
        before,address,memoryValue,store,entry,Tests.SubwordDecoderFixture.entry,Std.ExtHashMap.getElem_insert]
  have second : (operand sample).read (before sample) =
      .ok (if store sample then (0xdead12ab : BitVec 32) else memoryValue sample) (before sample) := by
    unfold operand
    split
    · apply Reference.RiscV.Sail.read_register
      simp [before,Std.ExtDHashMap.get?_insert]
    · exact memory
  have last : (target sample).read (before sample) =
      .ok (if store sample then memoryValue sample else if aliasing sample then sourceValue sample else 0) (before sample) := by
    fin_cases sample
    all_goals first
      | exact memory
      | exact first
      | rfl
      | (apply Reference.RiscV.Sail.read_register; simp [before,Std.ExtDHashMap.get?_insert,store,aliasing])
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (before sample) =
      .ok (0 : BitVec 32) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · fin_cases sample <;> decide
  · change initialImage (before sample) (cells sample) = some (seeds sample)
    by_cases aliases : aliasing sample = true
    · simp only [cells,seeds,aliases,ite_true,initialImage,List.mapM_cons,List.mapM_nil,first,second]
      rfl
    · simp only [cells,seeds,aliases,Bool.false_eq_true,ite_false,initialImage,List.mapM_cons,List.mapM_nil,first,second,last]
      rfl
  · rw [initialState,pc]
    rfl

end Tests.SubwordBoundsFixture
