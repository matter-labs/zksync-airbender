import Tests.MulDivDecoderCases
import Airbender.Review.Trace.Families.MulDiv.Theorems
import Airbender.Review.Trace.Families.MulDiv.History
import Airbender.Review.Trace.Families.MulDiv.Values
import Tests.MulDivMul
import Tests.MulDivMulhu
import Tests.MulDivDivu
import Tests.MulDivRemu

namespace Tests.MulDivInitializedFixture
open Airbender Arithmetic Trace Verification MulDiv
open Reference.RiscV.Sail

def dividend (zeroDivisor : Bool) : Nat := if zeroDivisor then 4294967295 else 123
def divisor (zeroDivisor : Bool) : Nat := if zeroDivisor then 0 else 7

def before (op : Operation) (discarded zeroDivisor : Bool) : State :=
  { (default : State) with
    mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 (BitVec.ofNat 8 (word op discarded).toNat)
      |>.insert 1 (BitVec.ofNat 8 ((word op discarded).toNat / 256))
      |>.insert 2 (BitVec.ofNat 8 ((word op discarded).toNat / 65536))
      |>.insert 3 (BitVec.ofNat 8 ((word op discarded).toNat / 16777216))
      |>.insert 4 0x73 |>.insert 5 0x10 |>.insert 6 0 |>.insert 7 0xc0)
    regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (BitVec.ofNat 32 (dividend zeroDivisor))
      |>.insert .x2 (BitVec.ofNat 32 (divisor zeroDivisor))
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32)
      |>.insert .misa (0x40001000 : BitVec 32)) }

private theorem public_word (op : Operation) (discarded zeroDivisor : Bool) :
    (Cell.ram 0).read (before op discarded zeroDivisor) =
      .ok (word op discarded) (before op discarded zeroDivisor) := by
  cases op <;> cases discarded <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      before,word,Operation.funct3,Std.ExtHashMap.getElem_insert]

private theorem public_hole (op : Operation) (discarded zeroDivisor : Bool) :
    (Cell.ram 4).read (before op discarded zeroDivisor) =
      .ok (0xc0001073 : BitVec 32) (before op discarded zeroDivisor) := by
  simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
    before,Std.ExtHashMap.getElem_insert]

theorem program_image (op : Operation) (discarded zeroDivisor : Bool) :
    MulDiv.sparseDecoderSetupImage (before op discarded zeroDivisor) 2 20 =
      some (setup op discarded) := by
  have isa : Reference.Sail.run (SailRV32.readReg .misa) (before op discarded zeroDivisor) =
      .ok (0x40001000 : BitVec 32) (before op discarded zeroDivisor) := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  have first : programSlotRunWith MulDiv.decoderFields (before op discarded zeroDivisor) 0 =
      some (some (entry op discarded)) := by
    simp only [programSlotRunWith,public_word,original_decode op discarded _ isa,
      bind,Option.bind,pure]
    cases op <;> cases discarded <;> rfl
  have hole : programSlotRunWith MulDiv.decoderFields (before op discarded zeroDivisor) 4 = some none := by
    simp only [programSlotRunWith,public_hole,bind,Option.bind,pure]
    exact decoded_hole (before op discarded zeroDivisor)
  change (([0,4] : List (BitVec 32)).mapM
    (programSlotRunWith MulDiv.decoderFields (before op discarded zeroDivisor))).bind
      (fun entries => some (SparseDecoderSetup.mk entries 1048574)) = _
  rw [List.mapM_cons,first,List.mapM_cons,hole,List.mapM_nil]
  rfl

def assignment (op : Operation) (discarded zeroDivisor : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 7 then (if discarded then 0 else 3)
  else MulDivWitness.assignment op (if zeroDivisor then 1 else 4) discarded i

def nativeRow (op : Operation) (discarded zeroDivisor : Bool) : Row mersenne31Modulus MulDivFamily :=
  ⟨.mulDiv,assignment op discarded zeroDivisor⟩
private def cell (register time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair register 0),(time,0),Nat.pair (value%65536) (value/65536)⟩
def trace (op : Operation) (discarded zeroDivisor : Bool) : Data mersenne31Modulus MulDivFamily where
  rows := [nativeRow op discarded zeroDivisor]
  rom := ()
  initial := ⟨(0,0),(4,0)⟩
  terminal := ⟨(4,0),(8,0)⟩
  initialMemory := [cell 0 0 0,cell 1 0 (dividend zeroDivisor),cell 2 0 (divisor zeroDivisor),cell 3 0 0]
  terminalMemory := [cell 0 (if discarded then 6 else 0) 0,
    cell 1 4 (dividend zeroDivisor),cell 2 5 (divisor zeroDivisor),
    cell 3 (if discarded then 0 else 6) (writtenWord (assignment op discarded zeroDivisor)).value]

/-- Changing only the decoder destination index leaves every local equation
    and query unchanged; full public lookup membership is checked separately. -/
theorem native_constraints (op : Operation) (discarded zeroDivisor : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment op discarded zeroDivisor))
      MulDiv.importedConstraints := by
  cases op
  · simpa [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,Lookup.Contains,range16,timestamp19,fixed3,Table.toRaw,
      ProvableType.fromElements] using MulDivMul.native_constraints (if zeroDivisor then 1 else 4) discarded
  · simpa [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,Lookup.Contains,range16,timestamp19,fixed3,Table.toRaw,
      ProvableType.fromElements] using MulDivMulhu.native_constraints (if zeroDivisor then 1 else 4) discarded
  · simpa [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,Lookup.Contains,range16,timestamp19,fixed3,Table.toRaw,
      ProvableType.fromElements] using MulDivDivu.native_constraints (if zeroDivisor then 1 else 4) discarded
  · simpa [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,assignment,Lookup.Contains,range16,timestamp19,fixed3,Table.toRaw,
      ProvableType.fromElements] using MulDivRemu.native_constraints (if zeroDivisor then 1 else 4) discarded

private abbrev MemoryMatches (candidate : Data mersenne31Modulus MulDivFamily) : Prop :=
  (candidate.initialMemory ++ candidate.rows.flatMap Row.writes).Perm
    (candidate.terminalMemory ++ candidate.rows.flatMap Row.reads)

private theorem memory_mul (discarded zeroDivisor : Bool) :
    MemoryMatches (trace .mul discarded zeroDivisor) := by
  cases discarded <;> cases zeroDivisor <;> decide +kernel
private theorem memory_mulhu (discarded zeroDivisor : Bool) :
    MemoryMatches (trace .mulhu discarded zeroDivisor) := by
  cases discarded <;> cases zeroDivisor <;> decide +kernel
private theorem memory_divu (discarded zeroDivisor : Bool) :
    MemoryMatches (trace .divu discarded zeroDivisor) := by
  cases discarded <;> cases zeroDivisor <;> decide +kernel
private theorem memory_remu (discarded zeroDivisor : Bool) :
    MemoryMatches (trace .remu discarded zeroDivisor) := by
  cases discarded <;> cases zeroDivisor <;> decide +kernel

theorem accepted (op : Operation) (discarded zeroDivisor : Bool) :
    Accepted (trace op discarded zeroDivisor) := by
  constructor
  · intro row member
    have same : row = nativeRow op discarded zeroDivisor := by simpa [trace] using member
    subst row
    exact native_constraints op discarded zeroDivisor
  · intro row member
    have same : row = nativeRow op discarded zeroDivisor := by simpa [trace] using member
    subst row
    cases op <;> cases discarded <;> cases zeroDivisor <;> decide
  · change [(trace op discarded zeroDivisor).initial,(nativeRow op discarded zeroDivisor).finish].Perm
      [(trace op discarded zeroDivisor).terminal,(nativeRow op discarded zeroDivisor).start]
    have start : (nativeRow op discarded zeroDivisor).start = (trace op discarded zeroDivisor).initial := by
      cases op <;> cases discarded <;> cases zeroDivisor <;> rfl
    have finish : (nativeRow op discarded zeroDivisor).finish = (trace op discarded zeroDivisor).terminal := by
      cases op <;> cases discarded <;> cases zeroDivisor <;> rfl
    rw [start,finish]
    exact List.Perm.swap _ _ []
  · cases op
    · exact memory_mul discarded zeroDivisor
    · exact memory_mulhu discarded zeroDivisor
    · exact memory_divu discarded zeroDivisor
    · exact memory_remu discarded zeroDivisor

theorem public_inputs (op : Operation) (discarded zeroDivisor : Bool) :
    ImageBoundary (trace op discarded zeroDivisor) (before op discarded zeroDivisor)
      [.register 0,.register 1,.register 2,.register 3] := by
  have zero : (Cell.register 0).read (before op discarded zeroDivisor) =
      .ok (0 : BitVec 32) (before op discarded zeroDivisor) := rfl
  have first : (Cell.register 1).read (before op discarded zeroDivisor) =
      .ok (BitVec.ofNat 32 (dividend zeroDivisor)) (before op discarded zeroDivisor) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 2).read (before op discarded zeroDivisor) =
      .ok (BitVec.ofNat 32 (divisor zeroDivisor)) (before op discarded zeroDivisor) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have third : (Cell.register 3).read (before op discarded zeroDivisor) =
      .ok (0 : BitVec 32) (before op discarded zeroDivisor) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (before op discarded zeroDivisor) =
      .ok (0 : BitVec 32) (before op discarded zeroDivisor) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  constructor
  · decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,first,second,third]
    cases zeroDivisor <;> rfl
  · rw [initialState,pc]
    rfl

private theorem assignment_query (op : Operation) (discarded zeroDivisor : Bool) :
    MulDiv.decoderQuery (assignment op discarded zeroDivisor) =
      (entry op discarded).query := by
  rw [entry_query]
  cases op <;> cases discarded <;> cases zeroDivisor <;>
    norm_num [MulDiv.decoderQuery,nativeDecoderQuery,MulDiv.importedConstraintsTraceColumns,
      MulDiv.importedConstraintsDecoderColumns,assignment,MulDivWitness.assignment,
      MulDivWitness.witnessValues,Operation.funct3,Operation.nativeMask]

theorem decoded (op : Operation) (discarded zeroDivisor : Bool) :
    MulDiv.Decoded (trace op discarded zeroDivisor) (setup op discarded) := by
  intro row member
  have same : row = nativeRow op discarded zeroDivisor := by simpa [trace] using member
  subst row
  rw [MulDiv.Proofs.row_decoder_query]
  change (setup op discarded).table.Contains #[] (MulDiv.decoderQuery (assignment op discarded zeroDivisor))
  rw [assignment_query]
  exact Trace.Proofs.sparse_head_member (entry op discarded) [none] 1048574

end Tests.MulDivInitializedFixture
