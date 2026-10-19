import Tests.ControlValues
import Airbender.Review.Trace.Families.JumpBranchSlt.Comparisons

namespace Tests.ControlComparisons
open Airbender Trace Verification Arithmetic Reference.RiscV.Sail

inductive Kind | slt | sltu | sltiu0 | slti deriving DecidableEq
namespace Kind
def index : Kind → Nat | .slt => 0 | .sltu => 1 | .sltiu0 => 2 | .slti => 3
def immediate : Kind → Bool | .sltiu0 | .slti => true | _ => false
def signed : Kind → Bool | .slt | .slti => true | _ => false
def zero : Kind → Bool | .sltiu0 => true | _ => false
def source (kind : Kind) : Nat := if kind.immediate then 123 else 4294967295
def result : Kind → Nat | .slt => 1 | _ => 0
def control : Kind → Nat | .slt | .sltiu0 => 1 | _ => 0
end Kind

/-- New logical original-byte fixture; its third SLTIU-to-x0 query is also
    retained in the previously certified native export. No new export is claimed. -/
def words : Vector (BitVec 32) 4 := #v[0x0020a1b3,0x0020b1b3,0xfff0b013,0xfff0a193]
def before (kind : Kind) : State :=
  { (default : State) with
    mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
    |>.insert 0 0xb3
    |>.insert 1 0xa1
    |>.insert 2 0x20
    |>.insert 3 0x0
    |>.insert 4 0xb3
    |>.insert 5 0xb1
    |>.insert 6 0x20
    |>.insert 7 0x0
    |>.insert 8 0x13
    |>.insert 9 0xb0
    |>.insert 10 0xf0
    |>.insert 11 0xff
    |>.insert 12 0x93
    |>.insert 13 0xa1
    |>.insert 14 0xf0
    |>.insert 15 0xff)
    regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (BitVec.ofNat 32 kind.source) |>.insert .x2 (1 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (BitVec.ofNat 32 (4 * kind.index))) }
def setup : SparseDecoderSetup Unit :=
  ⟨[some ⟨0,0x0020a1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLT),⟨(),1,2,3,⟨0,0⟩,4,2⟩⟩,
    some ⟨4,0x0020b1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLTU),⟨(),1,2,3,⟨0,0⟩,4,3⟩⟩,
    some ⟨8,0xfff0b013,.ITYPE (0xfff,.Regidx 1,.Regidx 0,.SLTIU),⟨(),1,0,0,⟨65535,65535⟩,8,3⟩⟩,
    some ⟨12,0xfff0a193,.ITYPE (0xfff,.Regidx 1,.Regidx 3,.SLTI),⟨(),1,0,3,⟨65535,65535⟩,8,2⟩⟩],1048572⟩

private theorem public_words (kind : Kind) (i : Fin 4) :
    (Cell.ram (BitVec.ofNat 32 (4 * (i.val)))).read (before kind) =
      .ok words[i.val] (before kind) := by
  fin_cases i <;> simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
    before,words,Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 65536 in
theorem program_image (kind : Kind) : JumpBranchSlt.sparseDecoderSetupImage (before kind) 4 20 = some setup := by
  have slots : ([0,4,8,12] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields (before kind)) = some setup.slots := by
    simp only [List.mapM_cons,List.mapM_nil,programSlotWith,
      show (Cell.ram 0).read (before kind) = .ok (0x0020a1b3 : BitVec 32) (before kind) from public_words kind ⟨0,by decide⟩,
      show (Cell.ram 4).read (before kind) = .ok (0x0020b1b3 : BitVec 32) (before kind) from public_words kind ⟨1,by decide⟩,
      show (Cell.ram 8).read (before kind) = .ok (0xfff0b013 : BitVec 32) (before kind) from public_words kind ⟨2,by decide⟩,
      show (Cell.ram 12).read (before kind) = .ok (0xfff0a193 : BitVec 32) (before kind) from public_words kind ⟨3,by decide⟩,
      bind,Option.bind]
    cbv
  change (([0,4,8,12] : List (BitVec 32)).mapM (programSlotWith JumpBranchSlt.decoderFields (before kind))).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048572)) = some setup
  rw [slots]
  rfl

def assignment (kind : Kind) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 4 * kind.index else if i = 2 then 4 else if i = 15 then 8
  else if i = 4 ∨ i = 5 ∨ i = 53 ∨ i = 56 ∨ i = 59 then 1
  else if i = 6 then if kind.immediate then 0 else 2
  else if i = 7 then if kind.zero then 0 else 3
  else if i = 8 then if kind.zero then 1 else 0
  else if i = 9 ∨ i = 10 then if kind.immediate then 65535 else 0
  else if i = 11 then if kind.signed then 2 else 3
  else if i = 12 then if kind.immediate then 8 else 4
  else if i = 13 ∨ i = 42 ∨ i = 48 then 4 * kind.index+4
  else if i = 19 ∨ i = 33 then if kind.immediate then 0 else 1
  else if i = 20 ∨ i = 28 ∨ i = 31 ∨ i = 49 then if kind.immediate then 1 else 0
  else if i = 22 then if kind.immediate then 123 else 65535
  else if i = 23 ∨ i = 27 then if kind.immediate then 0 else 65535
  else if i = 24 then if kind.immediate then 0 else 1
  else if i = 26 then if kind.immediate then 124 else 65534
  else if i = 30 then if kind.immediate then 1056423407 else 2147352572
  else if i = 32 then if kind.immediate then 32768 else 32767
  else if i = 34 then if kind.immediate then 32767 else 32768
  else if i = 35 then kind.control
  else if i = 37 then if kind.zero then 0 else 1
  else if i = 38 then kind.result
  else if i = 57 then if kind.zero then 5 else 0
  else 0

def nativeRow (kind : Kind) : Row mersenne31Modulus JumpBranchSltFamily := ⟨.jumpBranchSlt,assignment kind⟩
private def cell (register time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair register 0),(time,0),Nat.pair (value%65536) (value/65536)⟩
def trace (kind : Kind) : Data mersenne31Modulus JumpBranchSltFamily where
  rows := [nativeRow kind]
  rom := ()
  initial := ⟨(4 * kind.index,0),(4,0)⟩
  terminal := ⟨(4 * kind.index+4,0),(8,0)⟩
  initialMemory := [cell 0 0 0,cell 1 0 kind.source,cell 2 0 1,cell 3 0 0]
  terminalMemory := [cell 0 (if kind.zero then 6 else if kind.immediate then 5 else 0) 0,
    cell 1 4 kind.source,cell 2 (if kind.immediate then 0 else 5) 1,
    cell 3 (if kind.zero then 0 else 6) kind.result]

theorem native_constraints (kind : Kind) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment kind)) JumpBranchSlt.importedConstraints := by
  cases kind <;> simp [JumpBranchSlt.importedConstraints,FlatOperation.ConstraintsHoldFlat,
    Expression.eval,environment,assignment,Kind.immediate,Kind.zero,Kind.index,Kind.result,Kind.control]
  all_goals
    repeat' apply And.intro
    all_goals first | (apply range16_contains; decide) | (apply timestamp19_contains; decide) | try decide
    all_goals simp only [Lookup.Contains,fixed3,Table.toRaw,conditionalControlTable,
      jumpCleanupTable,Table.fromStatic,StaticTable.toTable,ProvableType.fromElements,
      Expression.eval,Vector.map_mk,List.map_toArray,List.map_cons,List.map_nil,assignment,
      Kind.immediate,Kind.signed,Kind.zero,Kind.index,Kind.result,Kind.control]
    all_goals solve
    | refine ⟨⟨34,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
    | refine ⟨⟨35,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
    | refine ⟨⟨75,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
    | refine ⟨⟨74,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
    | refine ⟨⟨4,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
    | refine ⟨⟨8,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
    | refine ⟨⟨12,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
    | refine ⟨⟨16,by decide⟩,?_⟩; norm_num [jumpCleanupRow]

theorem accepted (kind : Kind) : Accepted (trace kind) := by
  constructor
  · intro row member
    have eq : row = nativeRow kind := by simpa [trace] using member
    subst row
    exact native_constraints kind
  · intro row member
    have eq : row = nativeRow kind := by simpa [trace] using member
    subst row
    cases kind <;> decide
  · change [(trace kind).initial,(nativeRow kind).finish].Perm [(trace kind).terminal,(nativeRow kind).start]
    have start : (nativeRow kind).start = (trace kind).initial := by cases kind <;> rfl
    have finish : (nativeRow kind).finish = (trace kind).terminal := by cases kind <;> rfl
    rw [start,finish]
    exact List.Perm.swap _ _ []
  · cases kind <;> decide +kernel

theorem public_inputs (kind : Kind) :
    ImageBoundary (trace kind) (before kind) [.register 0,.register 1,.register 2,.register 3] := by
  have zero : (Cell.register 0).read (before kind) = .ok (0 : BitVec 32) (before kind) := rfl
  have first : (Cell.register 1).read (before kind) = .ok (BitVec.ofNat 32 kind.source) (before kind) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 2).read (before kind) = .ok (1 : BitVec 32) (before kind) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have third : (Cell.register 3).read (before kind) = .ok (0 : BitVec 32) (before kind) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (before kind) =
      .ok (BitVec.ofNat 32 (4 * kind.index)) (before kind) := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · cases kind <;> decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,first,second,third]
    cases kind <;> rfl
  · rw [initialState,pc]
    cases kind <;> rfl

theorem decoded (kind : Kind) : JumpBranchSlt.Decoded (trace kind) setup := by
  intro row member
  have eq : row = nativeRow kind := by simpa [trace] using member
  subst row
  cases kind
  · refine ⟨⟨0,by decide⟩,?_⟩; decide +kernel
  · refine ⟨⟨1,by decide⟩,?_⟩; decide +kernel
  · refine ⟨⟨2,by decide⟩,?_⟩; decide +kernel
  · refine ⟨⟨3,by decide⟩,?_⟩; decide +kernel

theorem public_results (kind : Kind) :
    (Word.mk ((assignment kind) 38).val ((assignment kind) 39).val).value = kind.result := by
  have result := JumpBranchSlt.public_comparisons (program_image kind) (public_inputs kind)
    (accepted kind) (decoded kind) (nativeRow kind) (by simp [trace]) (by cases kind <;> decide)
  exact result.trans (by cases kind <;> decide)

/-- Same negative register input: signed comparison is true and unsigned false. -/
theorem signed_unsigned_differ :
    (Word.mk (assignment .slt 38).val (assignment .slt 39).val).value = 1 ∧
    (Word.mk (assignment .sltu 38).val (assignment .sltu 39).val).value = 0 :=
  ⟨public_results .slt,public_results .sltu⟩

/-- Negative sign-extended immediate: unsigned raw result one is discarded at x0;
    the signed comparison with the same positive source is false. -/
theorem immediate_and_mask : assignment .sltiu0 35 = 1 ∧ assignment .sltiu0 38 = 0 ∧
    (Word.mk (assignment .slti 38).val (assignment .slti 39).val).value = 0 :=
  ⟨by decide,by decide,public_results .slti⟩

theorem exported_sltiu : ∃ i : Fin 1048576,
    JumpBranchSlt.decoderQuery (assignment .sltiu0) = JumpBranchSlt.NativeSetup.controlDecoder.row i :=
  ⟨⟨2,by decide⟩,by decide +kernel⟩

/-- Reversing the native positive flag can preserve its field equation only by
    using an out-of-range shifted limb. The actual scalar query rejects it. -/
def badPositive (i : Nat) : ZMod mersenne31Modulus :=
  if i = 31 then 1 else if i = 32 then 98303 else assignment .sltu i

theorem bad_positive_equation :
    Expression.eval (environment badPositive)
      (FlatOperation.constraints JumpBranchSlt.importedConstraints)[18] = 0 := by decide +kernel

theorem bad_positive_rejected :
    ¬FlatOperation.ConstraintsHoldFlat (environment badPositive) JumpBranchSlt.importedConstraints := by
  intro holds
  have bound := range16_bound (lookup_of_holds holds ⟨2,by rw [JumpBranchSlt.Proofs.lookup_count]; decide⟩)
  change (98303 : ZMod mersenne31Modulus).val < 65536 at bound
  exact (by decide : ¬(98303 : ZMod mersenne31Modulus).val < 65536) bound

end Tests.ControlComparisons
