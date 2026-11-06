import Tests.NativeReducedWitness
import Airbender.Proofs.ShiftBinop.NativeSetup
import Airbender.Proofs.Sail.DecoderFrame

namespace Tests.NativeReducedFixture
open Airbender Arithmetic Trace ReducedMachine Native
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def publicPC (discarded : Bool) : BitVec 32 := if discarded then 48 else 0

-- Reuse original public bytes/misa only; no old split decoder metadata/table.
def before (discarded : Bool) : State :=
  { ShiftBinop.NativeSetup.before with regs := (ShiftBinop.NativeSetup.before.regs
      |>.insert .x1 (1 : BitVec 32) |>.insert .x2 (1 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (publicPC discarded)) }

def nativeRow (discarded : Bool) : Row mersenne31Modulus NativeReducedFamily :=
  ⟨.reduced,NativeReducedWitness.assignment discarded⟩

private def cell (register time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair register 0),(time,0),Nat.pair (value%65536) (value/65536)⟩

def trace (discarded : Bool) : Data mersenne31Modulus NativeReducedFamily where
  rows := [nativeRow discarded]
  rom := NativeFixed.table
  initial := PCState.boundary (publicPC discarded) (4,0)
  terminal := PCState.boundary (publicPC discarded + 4) (8,0)
  initialMemory := [cell 0 0 0,cell 1 0 1,cell 2 0 1,cell 3 0 0]
  terminalMemory := [cell 0 (if discarded then 6 else 0) 0,cell 1 4 1,cell 2 5 1,
    cell 3 (if discarded then 0 else 6) (if discarded then 0 else 2)]

private theorem state_ext (a b : PCState.State mersenne31Modulus)
    (pc : a.pc = b.pc) (timestamp : a.timestamp = b.timestamp) : a = b := by
  cases a
  cases b
  cases pc
  cases timestamp
  rfl

/-- Actual117-equation/all22-lookup rows plus imported active/state/memory
    matching. Every native source/read/write participates, including discarded x0. -/
theorem accepted (discarded : Bool) : Accepted (fixedData (trace discarded)) := by
  constructor
  · intro row present
    have same : row = nativeRow discarded := by simpa [fixedData,trace] using present
    subst row
    exact NativeReducedWitness.native_constraints discarded
  · intro row present
    have same : row = nativeRow discarded := by simpa [fixedData,trace] using present
    subst row
    cases discarded <;> decide +kernel
  · change [(trace discarded).initial,(nativeRow discarded).finish].Perm
      [(trace discarded).terminal,(nativeRow discarded).start]
    have start : (nativeRow discarded).start = (trace discarded).initial := by
      apply state_ext
      · cases discarded <;> decide +kernel
      · cases discarded <;> decide +kernel
    have finish : (nativeRow discarded).finish = (trace discarded).terminal := by
      apply state_ext
      · cases discarded <;> decide +kernel
      · cases discarded <;> decide +kernel
    rw [start,finish]
    exact List.Perm.swap _ _ []
  · cases discarded <;> decide +kernel

/-- All public seeds/PC are extracted from original Sail reads; no desired
    intermediate state or expected read/write value is a theorem premise. -/
theorem public_inputs (discarded : Bool) :
    ImageBoundary (fixedData (trace discarded)) (before discarded)
      [.register 0,.register 1,.register 2,.register 3] := by
  have zero : (Cell.register 0).read (before discarded) = .ok (0 : BitVec 32) (before discarded) := rfl
  have first : (Cell.register 1).read (before discarded) = .ok (1 : BitVec 32) (before discarded) := by
    apply read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 2).read (before discarded) = .ok (1 : BitVec 32) (before discarded) := by
    apply read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have third : (Cell.register 3).read (before discarded) = .ok (0 : BitVec 32) (before discarded) := by
    apply read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have pc : run (SailRV32.Functions.get_arch_pc ()) (before discarded) =
      .ok (publicPC discarded) (before discarded) := by
    apply read_register
    simp [before]
  constructor
  · decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,first,second,third]
    rfl
  · rw [initialState,pc]
    rfl

private def slot (i : Fin 13) : Option ShiftProgramEntry :=
  (shiftDecoderFields ShiftBinop.NativeSetup.instructions[i.val]).map fun data =>
    ⟨BitVec.ofNat 32 (4 * i.val),ShiftBinop.NativeSetup.words[i.val],
      ShiftBinop.NativeSetup.instructions[i.val],data⟩

def setup : SparseDecoderSetup ShiftMode := ⟨(List.finRange 13).map slot,3⟩

private theorem public_words (discarded : Bool) (i : Fin 25) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (before discarded) =
      .ok ShiftBinop.NativeSetup.words[i.val] (before discarded) :=
  read_word_frame (before := ShiftBinop.NativeSetup.before) (after := before discarded)
    rfl (ShiftBinop.Proofs.native_fixture_words i)

private theorem public_decode (discarded : Bool) (i : Fin 25) :
    run (SailRV32.Functions.encdec_backwards ShiftBinop.NativeSetup.words[i.val]) (before discarded) =
      .ok ShiftBinop.NativeSetup.instructions[i.val] (before discarded) := by
  apply (Reference.Sail.decoded_misa_frame _ (ShiftBinop.Proofs.native_fixture_decode i)).2
  simp [before,Std.ExtDHashMap.get?_insert]

private theorem public_slot (discarded : Bool) (i : Fin 13) :
    programSlotRunWith shiftDecoderFields (before discarded) (BitVec.ofNat 32 (4 * i.val)) =
      some (setup.slots[i.val]'(by change i.val < 13; exact i.isLt)) := by
  simp only [programSlotRunWith,public_words discarded ⟨i.val,by omega⟩,
    public_decode discarded ⟨i.val,by omega⟩,bind,Option.bind,pure]
  fin_cases i <;> rfl

/-- Full original public sparse/padded setup construction, including unsupported
    holes and three padding rows. Native masks/fields are newly projected. -/
theorem program_image (discarded : Bool) :
    shiftDecoderSetupImage (before discarded) 13 4 = some setup := by
  change (([0,4,8,12,16,20,24,28,32,36,40,44,48] : List (BitVec 32)).mapM
    (programSlotRunWith shiftDecoderFields (before discarded))).bind
      (fun slots => some (SparseDecoderSetup.mk slots 3)) = some setup
  simp only [List.mapM_cons,List.mapM_nil,
    show programSlotRunWith shiftDecoderFields (before discarded) 0 = some (setup.slots[0])
      from public_slot discarded ⟨0,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 4 = some (setup.slots[1])
      from public_slot discarded ⟨1,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 8 = some (setup.slots[2])
      from public_slot discarded ⟨2,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 12 = some (setup.slots[3])
      from public_slot discarded ⟨3,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 16 = some (setup.slots[4])
      from public_slot discarded ⟨4,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 20 = some (setup.slots[5])
      from public_slot discarded ⟨5,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 24 = some (setup.slots[6])
      from public_slot discarded ⟨6,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 28 = some (setup.slots[7])
      from public_slot discarded ⟨7,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 32 = some (setup.slots[8])
      from public_slot discarded ⟨8,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 36 = some (setup.slots[9])
      from public_slot discarded ⟨9,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 40 = some (setup.slots[10])
      from public_slot discarded ⟨10,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 44 = some (setup.slots[11])
      from public_slot discarded ⟨11,by decide⟩,
    show programSlotRunWith shiftDecoderFields (before discarded) 48 = some (setup.slots[12])
      from public_slot discarded ⟨12,by decide⟩,bind,Option.bind,pure]
  rfl

/-- Exact membership at the imported native ten-field query; x0 instructions
    remain their original source/rd/opcode, not rewritten neutral instructions. -/
theorem decoded (discarded : Bool) : ShiftDecodedTrace (fixedData (trace discarded)) setup := by
  intro row present
  have same : row = nativeRow discarded := by simpa [fixedData,trace] using present
  subst row
  rw [NativeShiftDecoderProofs.row_query]
  cases discarded
  · refine ⟨⟨0,by change 0 < 16; decide⟩,?_⟩
    decide +kernel
  · refine ⟨⟨12,by change 12 < 16; decide⟩,?_⟩
    decide +kernel

end Tests.NativeReducedFixture
