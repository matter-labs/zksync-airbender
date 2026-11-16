module
public import Human.Trace.Machine.Model
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Trace Arithmetic
set_option warningAsError true

/-- Public instruction addresses and encodings for a copy loop with two bigint calls. -/
def code (index : Fin 12) : Nat × Nat :=
  match index.val with
  | 0 => (0, 0x00200293) | 1 => (4, 0x02000537) | 2 => (8, 0x02050593)
  | 3 => (12, 0x00700113) | 4 => (16, 0x0025a023) | 5 => (20, 0x06c0006f)
  | 6 => (128, 0x00000617) | 7 => (132, 0x7ca01073) | 8 => (136, 0xfff28293)
  | 9 => (140, 0xfe029ae3) | 10 => (144, 0x008000ef) | _ => (152, 0x00808067)

/-- The code word at an aligned address. Other words are unsupported zero encodings. -/
def codeBits (address : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((List.finRange 12).find? fun index => (code index).1 == address).map
    (fun index => (code index).2) |>.getD 0)

/-- Zero registers and RAM with the public instruction bytes in ROM. -/
def initial : RV.State where
  pc := 0
  regFile _ := 0
  rom address := (codeBits (address.toNat / 4 * 4)).extractLsb' (8 * (address.toNat % 4)) 8
  mem _ := 0

/-- Production decoding determines all metadata of each public instruction. -/
def entry (index : Fin 12) : RVMachineProgramEntry :=
  (rvMachineProgramEntryWith .unified initial (BitVec.ofNat 32 (code index).1)).get
    (by fin_cases index <;> decide +kernel)

/-- Every distinct code location occurs once in the public program. -/
def program : List RVMachineProgramEntry := (List.finRange 12).map entry

/-- Native execution revisits the loop body and its bigint call. -/
def codeIndex (index : Fin 16) : Fin 12 :=
  match index.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7
  | 8 => 8 | 9 => 9 | 10 => 6 | 11 => 7 | 12 => 8 | 13 => 9 | 14 => 10 | _ => 11

/-- The row metadata is the public instruction metadata at its native occurrence. -/
def metadata (index : Fin 16) : RVMachineDecoderData := (entry (codeIndex index)).data

def destinationAddress : BitVec 32 := 33554432
def sourceAddress : BitVec 32 := 33554464

/-- The finite transfer domain contains all registers and two separate eight-word buffers. -/
def finiteCells : List Cell :=
  registerCells ++ (List.finRange 16).map fun index =>
    .ram (destinationAddress + 4 * BitVec.ofNat 32 index.val)

/-- One CPU occurrence supplies instruction data, port words and predecessor clocks. -/
structure Sample where
  /-- The instruction starts at this PC. -/
  pc : Nat
  /-- The instruction finishes at this PC. -/
  next : Nat
  /-- The instruction starts at this occurrence clock. -/
  clock : Nat
  /-- The first source port reads this predecessor clock. -/
  previous0 : Nat
  /-- The second source port reads this predecessor clock. -/
  previous1 : Nat
  /-- The destination port reads this predecessor clock. -/
  previous2 : Nat
  /-- The first source port reads this word. -/
  source0 : Nat
  /-- The second source port reads this word. -/
  source1 : Nat
  /-- The destination port reads this old word. -/
  oldDestination : Nat
  /-- The destination port writes this new word. -/
  newDestination : Nat

/-- Concrete candidate port values and recomputed predecessor clocks. The
acceptance proof checks these against the actual imported port expressions. -/
def sample (index : Fin 16) : Sample :=
  match index.val with
  | 0 => ⟨0, 4, 4, 0, 4, 0, 0, 0, 0, 2⟩
  | 1 => ⟨4, 8, 8, 5, 8, 0, 0, 0, 0, 33554432⟩
  | 2 => ⟨8, 12, 12, 10, 9, 0, 33554432, 0, 0, 33554464⟩
  | 3 => ⟨12, 16, 16, 13, 16, 0, 0, 0, 0, 7⟩
  | 4 => ⟨16, 20, 20, 14, 18, 0, 33554464, 7, 0, 7⟩
  | 5 => ⟨20, 128, 24, 17, 24, 25, 0, 0, 0, 0⟩
  | 6 => ⟨128, 132, 28, 26, 28, 0, 0, 0, 0, 128⟩
  | 7 => ⟨132, 136, 32, 29, 0, 32, 0, 0, 0, 0⟩
  | 8 => ⟨136, 140, 36, 6, 34, 36, 2, 0, 2, 1⟩
  | 9 => ⟨140, 128, 40, 38, 37, 41, 1, 0, 0, 0⟩
  | 10 => ⟨128, 132, 44, 42, 44, 35, 0, 0, 0, 128⟩
  | 11 => ⟨132, 136, 48, 45, 0, 48, 0, 0, 0, 0⟩
  | 12 => ⟨136, 140, 52, 40, 50, 52, 1, 0, 1, 0⟩
  | 13 => ⟨140, 144, 56, 54, 53, 57, 0, 0, 0, 0⟩
  | 14 => ⟨144, 152, 60, 58, 60, 0, 0, 0, 0, 148⟩
  | _ => ⟨152, 156, 64, 62, 61, 65, 148, 0, 0, 0⟩

def family2 (index : Fin 16) : Bool :=
  index.val = 5 || index.val = 9 || index.val = 13 || index.val = 14 || index.val = 15
def branch (index : Fin 16) : Bool := index.val = 9 || index.val = 13
def indirect (index : Fin 16) : Bool := index.val = 15
def branchTaken (index : Fin 16) : Bool := index.val = 9
def saved (index : Fin 16) : Nat :=
  if branch index then (sample index).source0 else (sample index).pc + 4

/-- The unified assignment supplies all arithmetic, register, lookup and timestamp columns.
    Word limbs use natural-number quotients and remainders. -/
def machineAssignment (index : Fin 16) (column : Nat) : ZMod babyBearModulus :=
  let row := sample index
  let fields := metadata index
  if column = 0 then row.pc
  else if column = 2 then row.clock
  else if column = 4 || column = 123 || column = 124 || column = 125 then 1
  else if column = 5 then fields.rs1
  else if column = 6 then if index.val = 7 || index.val = 11 then 0x7ca else fields.rs2
  else if column = 7 then fields.rd
  else if column = 8 then fields.immediate.lo
  else if column = 9 then fields.immediate.hi
  else if column = 10 then fields.funct3
  else if 11 ≤ column && column ≤ 29 then if fields.mask.testBit (column - 11) then 1 else 0
  else if column = 30 then row.next
  else if column = 32 then row.clock + 4
  else if column = 34 then row.previous0
  else if column = 36 then ((row.source0 % 65536 : Nat) : ZMod babyBearModulus)
  else if column = 37 then ((row.source0 / 65536 : Nat) : ZMod babyBearModulus)
  else if column = 38 then if index.val = 7 || index.val = 11 then 0x7ca else fields.rs2
  else if column = 40 then row.previous1
  else if column = 42 then ((row.source1 % 65536 : Nat) : ZMod babyBearModulus)
  else if column = 43 then ((row.source1 / 65536 : Nat) : ZMod babyBearModulus)
  else if column = 44 then if index.val = 4 then 32 else fields.rd
  else if column = 45 then if index.val = 4 then 512 else 0
  else if column = 46 then row.previous2
  else if column = 48 then ((row.oldDestination % 65536 : Nat) : ZMod babyBearModulus)
  else if column = 49 then ((row.oldDestination / 65536 : Nat) : ZMod babyBearModulus)
  else if column = 50 then ((row.newDestination % 65536 : Nat) : ZMod babyBearModulus)
  else if column = 51 then ((row.newDestination / 65536 : Nat) : ZMod babyBearModulus)
  else if column = 52 || column = 53 then if index.val = 8 || index.val = 12 then 1 else 0
  else if column = 54 || column = 55 then if branchTaken index then 1 else 0
  else if column = 57 then if index.val = 4 then 32 else if index.val = 13 then 1 else 0
  else if column = 58 then if index.val = 4 then 512 else 0
  else if column = 59 || column = 79 || column = 106 then if branchTaken index then 1 else 0
  else if column = 64 || column = 114 || column = 116 then if family2 index then row.next else 0
  else if column = 74 then if index.val = 4 then 8 else if family2 index then saved index else 0
  else if column = 78 then (row.source0 : ZMod babyBearModulus) * row.source1 * 943718400
  else if column = 80 then if index.val = 4 then 448 else 0
  else if column = 82 then if family2 index then 1 else 0
  else if column = 83 then if family2 index then saved index else 0
  else if column = 84 then if index.val = 13 then 1 else 0
  else if column = 86 || column = 95 then if family2 index then 5 else 0
  else if column = 104 then if family2 index then 51 else 0
  else if column = 105 then if index.val = 9 then 16 else if index.val = 13 then 24 else 0
  else if column = 113 then if family2 index then 2 else 0
  else 0

def machineRows : List (Row babyBearModulus UnifiedFamily) :=
  (List.finRange 16).map fun index => ⟨.machine, machineAssignment index⟩

/-- Each actual COPY worker consumes x12=128, copies the nonzero right operand,
and returns zero control. The constructed command selects COPY; arbitrary accepted controls have separate semantics. -/
def workerAssignment (index : Fin 2) (column : Nat) : ZMod babyBearModulus :=
  if column = 0 || column = 66 || column = 212 || column = 214 || column = 215 then 1
  else if column = 1 then if index.val = 0 then 33 else 49
  else if column = 4 || column = 38 then 512
  else if column = 37 then 32
  else if column = 55 then 128
  else if column = 5 || column = 99 then if index.val = 0 then 0 else 7
  else if column = 7 || column = 39 || column = 67 || column = 115 || column = 194 then 7
  else if column = 131 || column = 163 then if index.val = 0 then 0 else 49
  else if 216 ≤ column && column < 273 then
    if (column - 216) % 3 = 2 then 1
    else if (column - 216) % 3 = 1 then 0
    else if index.val = 1 then if column = 270 then 46 else 35
    else if column = 216 then 12
    else if column = 243 then 20
    else if column = 246 then 22
    else if column = 270 then 30
    else 0
  else 0

def workerRows : List (Delegation.Row babyBearModulus) :=
  (List.finRange 2).map fun index => ⟨.bigint, workerAssignment index⟩

def old (cell : Cell) : MemoryToken babyBearModulus := cell.initialToken 0

def final (cell : Cell) : MemoryToken babyBearModulus :=
  match cell with
  | .register register =>
    let stamp := if register = 0 then 66 else if register = 1 then 64
      else if register = 2 then 21 else if register = 5 then 56
      else if register = 10 || register = 11 || register = 12 then 51 else 0
    let value : Word := if register = 1 then ⟨148, 0⟩ else if register = 2 then ⟨7, 0⟩
      else if register = 10 then ⟨0, 512⟩ else if register = 11 then ⟨32, 512⟩ else ⟨0, 0⟩
    ⟨cell.addressCode, (stamp, 0), Nat.pair value.lo value.hi⟩
  | .ram address =>
    if 33554432 ≤ address.toNat && address.toNat < 33554496 then
      ⟨cell.addressCode, (51, 0), Nat.pair
        (if address = destinationAddress ||
          address = sourceAddress then 7 else 0) 0⟩
    else old cell


/-- The submitted standard pool contains both COPY workers. The split pool is empty. -/
noncomputable def workers : Trace.Machine.WorkerPools babyBearModulus where
  standard := ⟨Delegation.modeledSetup Keccak.Controller.rows, workerRows, [], []⟩
  split := ⟨[], [], []⟩

/-- The finite transfer domain records all CPU and worker memory steps. -/
noncomputable def finiteTrace : UnifiedTrace babyBearModulus where
  rows := machineRows
  rom := UnifiedReduced.Setup.tableRV initial
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 156 (68, 0)
  initialMemory := finiteCells.map old
  terminalMemory := finiteCells.map final

/-- Architectural steps include CPU and both submitted worker occurrences. -/
noncomputable def steps := Trace.Machine.unifiedSteps finiteTrace ++ workers.steps

end Airbender.NonVacuous.DynamicCopyLoop
