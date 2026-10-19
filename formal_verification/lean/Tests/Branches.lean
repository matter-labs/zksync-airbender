import Tests.ControlValues
import Airbender.Review.Trace.Families.JumpBranchSlt.Branches

namespace Tests.Branches
open Airbender Trace Verification Arithmetic Reference.RiscV.Sail

inductive Mode | negative | positive | equal deriving DecidableEq
namespace Mode
def left : Mode → Nat | .negative => 4294967295 | _ => 1
def right : Mode → Nat | .positive => 4294967295 | _ => 1
end Mode
inductive Op | beq | bne | blt | bge | bltu | bgeu deriving DecidableEq
namespace Op
def index : Op → Nat | .beq => 0 | .bne => 1 | .blt => 2 | .bge => 3 | .bltu => 4 | .bgeu => 5
def tag : Op → Nat | .beq => 0 | .bne => 1 | .blt => 4 | .bge => 5 | .bltu => 6 | .bgeu => 7
def result (op : Op) (mode : Mode) : Nat := match mode,op with
  | .negative,.bne | .negative,.blt | .negative,.bgeu => 1
  | .positive,.bne | .positive,.bge | .positive,.bltu => 1
  | .equal,.beq | .equal,.bge | .equal,.bgeu => 1
  | _,_ => 0
def finish (mode : Mode) (op : Op) : Nat := 4 * op.index + (if op.result mode = 1 then 8 else 4)
end Op

/-- Six original branch words, each with offset eight. These logical bytes have
    no new native program-export certificate. -/
def words : Vector (BitVec 32) 6 := #v[0x208463,0x209463,0x20c463,0x20d463,0x20e463,0x20f463]
def before : State := { (default : State) with
  mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
    |>.insert 0 0x63
    |>.insert 1 0x84
    |>.insert 2 0x20
    |>.insert 3 0x0
    |>.insert 4 0x63
    |>.insert 5 0x94
    |>.insert 6 0x20
    |>.insert 7 0x0
    |>.insert 8 0x63
    |>.insert 9 0xc4
    |>.insert 10 0x20
    |>.insert 11 0x0
    |>.insert 12 0x63
    |>.insert 13 0xd4
    |>.insert 14 0x20
    |>.insert 15 0x0
    |>.insert 16 0x63
    |>.insert 17 0xe4
    |>.insert 18 0x20
    |>.insert 19 0x0
    |>.insert 20 0x63
    |>.insert 21 0xf4
    |>.insert 22 0x20
    |>.insert 23 0x0) }
def initial (mode : Mode) (op : Op) : State := { before with
  regs := (Std.ExtDHashMap.emptyWithCapacity |>.insert .x1 (BitVec.ofNat 32 mode.left)
    |>.insert .x2 (BitVec.ofNat 32 mode.right) |>.insert .PC (BitVec.ofNat 32 (4 * op.index))) }
def setup : SparseDecoderSetup Unit := ⟨[some ⟨0,0x208463,.BTYPE (8,.Regidx 2,.Regidx 1,.BEQ),⟨(),1,2,0,⟨8,0⟩,16,0⟩⟩,
    some ⟨4,0x209463,.BTYPE (8,.Regidx 2,.Regidx 1,.BNE),⟨(),1,2,0,⟨8,0⟩,16,1⟩⟩,
    some ⟨8,0x20c463,.BTYPE (8,.Regidx 2,.Regidx 1,.BLT),⟨(),1,2,0,⟨8,0⟩,16,4⟩⟩,
    some ⟨12,0x20d463,.BTYPE (8,.Regidx 2,.Regidx 1,.BGE),⟨(),1,2,0,⟨8,0⟩,16,5⟩⟩,
    some ⟨16,0x20e463,.BTYPE (8,.Regidx 2,.Regidx 1,.BLTU),⟨(),1,2,0,⟨8,0⟩,16,6⟩⟩,
    some ⟨20,0x20f463,.BTYPE (8,.Regidx 2,.Regidx 1,.BGEU),⟨(),1,2,0,⟨8,0⟩,16,7⟩⟩],1048570⟩

set_option maxRecDepth 65536 in
theorem program_image (mode : Mode) (op : Op) :
    JumpBranchSlt.sparseDecoderSetupImage (initial mode op) 6 20 = some setup := by
  have public_words (i : Fin 6) : (Cell.ram (BitVec.ofNat 32 (4 * (i.val)))).read (initial mode op) =
      .ok words[i.val] (initial mode op) := by
    fin_cases i <;> simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      initial,before,words,Std.ExtHashMap.getElem_insert]
  have slots : ([0,4,8,12,16,20] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields (initial mode op)) = some setup.slots := by
    simp only [List.mapM_cons,List.mapM_nil,programSlotWith,
      show (Cell.ram 0).read (initial mode op) = .ok (0x208463 : BitVec 32) (initial mode op) from public_words ⟨0,by decide⟩,
      show (Cell.ram 4).read (initial mode op) = .ok (0x209463 : BitVec 32) (initial mode op) from public_words ⟨1,by decide⟩,
      show (Cell.ram 8).read (initial mode op) = .ok (0x20c463 : BitVec 32) (initial mode op) from public_words ⟨2,by decide⟩,
      show (Cell.ram 12).read (initial mode op) = .ok (0x20d463 : BitVec 32) (initial mode op) from public_words ⟨3,by decide⟩,
      show (Cell.ram 16).read (initial mode op) = .ok (0x20e463 : BitVec 32) (initial mode op) from public_words ⟨4,by decide⟩,
      show (Cell.ram 20).read (initial mode op) = .ok (0x20f463 : BitVec 32) (initial mode op) from public_words ⟨5,by decide⟩,bind,Option.bind]
    cbv
  change (([0,4,8,12,16,20] : List (BitVec 32)).mapM
    (programSlotWith JumpBranchSlt.decoderFields (initial mode op))).bind
      (fun entries => some (SparseDecoderSetup.mk entries 1048570)) = some setup
  rw [slots]
  rfl

def assignment (mode : Mode) (op : Op) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 4 * op.index else if i = 2 then 4 else if i = 15 then 8
  else if i = 4 ∨ i = 5 ∨ i = 8 ∨ i = 21 ∨ i = 53 ∨ i = 56 ∨ i = 59 then 1
  else if i = 6 then 2 else if i = 9 then 8 else if i = 11 then op.tag else if i = 12 then 16
  else if i = 13 ∨ i = 42 ∨ i = 48 then op.finish mode
  else if i = 22 then (mode.left % 65536 : Nat) else if i = 23 then (mode.left / 65536 : Nat)
  else if i = 24 then (mode.right % 65536 : Nat) else if i = 25 then (mode.right / 65536 : Nat)
  else if i = 26 then match mode with | .negative => 65534 | .positive => 2 | .equal => 0
  else if i = 27 then match mode with | .negative => 65535 | _ => 0
  else if i = 28 ∨ i = 49 then match mode with | .positive => 1 | _ => 0
  else if i = 29 then match mode with | .equal => 1 | _ => 0
  else if i = 30 then match mode with | .negative => 2147352572 | .positive => 1073741824 | .equal => 0
  else if i = 31 then match mode with | .negative => 0 | _ => 1
  else if i = 32 then match mode with | .negative => 32767 | _ => 32768
  else if i = 33 then match mode with | .positive => 0 | _ => 1
  else if i = 34 then match mode with | .positive => 32767 | _ => 32768
  else if i = 35 ∨ i = 46 then op.result mode
  else if i = 45 then 1-op.result mode
  else 0

def nativeRow (mode : Mode) (op : Op) : Row mersenne31Modulus JumpBranchSltFamily :=
  ⟨.jumpBranchSlt,assignment mode op⟩
private def cell (register time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair register 0),(time,0),Nat.pair (value%65536) (value/65536)⟩
def trace (mode : Mode) (op : Op) : Data mersenne31Modulus JumpBranchSltFamily where
  rows := [nativeRow mode op]
  rom := ()
  initial := ⟨(4 * op.index,0),(4,0)⟩
  terminal := ⟨(op.finish mode,0),(8,0)⟩
  initialMemory := [cell 0 0 0,cell 1 0 mode.left,cell 2 0 mode.right]
  terminalMemory := [cell 0 6 0,cell 1 4 mode.left,cell 2 5 mode.right]

private theorem negative_native (op : Op) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment .negative op)) JumpBranchSlt.importedConstraints := by
  cases op
  all_goals
    apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
    constructor
    · simp only [JumpBranchSlt.importedConstraints,FlatOperation.constraints,
        List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first | (intro a bad; cases bad) | decide +kernel
    · simp only [JumpBranchSlt.importedConstraints,FlatOperation.lookups,
        List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first | (intro a bad; cases bad) | (apply range16_contains; decide +kernel) | (apply timestamp19_contains; decide +kernel) | skip
      all_goals simp only [Lookup.Contains,fixed3,Table.toRaw,conditionalControlTable,
        jumpCleanupTable,Table.fromStatic,StaticTable.toTable,ProvableType.fromElements,
        Expression.eval,Vector.map_mk,List.map_toArray,List.map_cons,List.map_nil,
        environment,assignment,Mode.left,Mode.right,Op.index,Op.tag,Op.finish,Op.result]
      all_goals solve
      | refine ⟨⟨32,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨33,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨36,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨37,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨38,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨39,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨4,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨8,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨12,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨16,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨20,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨24,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨28,by decide⟩,?_⟩; norm_num [jumpCleanupRow]

private theorem positive_native (op : Op) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment .positive op)) JumpBranchSlt.importedConstraints := by
  cases op
  all_goals
    apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
    constructor
    · simp only [JumpBranchSlt.importedConstraints,FlatOperation.constraints,
        List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first | (intro a bad; cases bad) | decide +kernel
    · simp only [JumpBranchSlt.importedConstraints,FlatOperation.lookups,
        List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first | (intro a bad; cases bad) | (apply range16_contains; decide +kernel) | (apply timestamp19_contains; decide +kernel) | skip
      all_goals simp only [Lookup.Contains,fixed3,Table.toRaw,conditionalControlTable,
        jumpCleanupTable,Table.fromStatic,StaticTable.toTable,ProvableType.fromElements,
        Expression.eval,Vector.map_mk,List.map_toArray,List.map_cons,List.map_nil,
        environment,assignment,Mode.left,Mode.right,Op.index,Op.tag,Op.finish,Op.result]
      all_goals solve
      | refine ⟨⟨72,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨73,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨76,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨77,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨78,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨79,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨4,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨8,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨12,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨16,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨20,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨24,by decide⟩,?_⟩; norm_num [jumpCleanupRow]

private theorem equal_native (op : Op) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment .equal op)) JumpBranchSlt.importedConstraints := by
  cases op
  all_goals
    apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
    constructor
    · simp only [JumpBranchSlt.importedConstraints,FlatOperation.constraints,
        List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first | (intro a bad; cases bad) | decide +kernel
    · simp only [JumpBranchSlt.importedConstraints,FlatOperation.lookups,
        List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first | (intro a bad; cases bad) | (apply range16_contains; decide +kernel) | (apply timestamp19_contains; decide +kernel) | skip
      all_goals simp only [Lookup.Contains,fixed3,Table.toRaw,conditionalControlTable,
        jumpCleanupTable,Table.fromStatic,StaticTable.toTable,ProvableType.fromElements,
        Expression.eval,Vector.map_mk,List.map_toArray,List.map_cons,List.map_nil,
        environment,assignment,Mode.left,Mode.right,Op.index,Op.tag,Op.finish,Op.result]
      all_goals solve
      | refine ⟨⟨16,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨17,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨20,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨21,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨22,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨23,by decide⟩,?_⟩; norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨4,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨8,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨12,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨16,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨20,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨24,by decide⟩,?_⟩; norm_num [jumpCleanupRow]
      | refine ⟨⟨28,by decide⟩,?_⟩; norm_num [jumpCleanupRow]

theorem native_constraints (mode : Mode) (op : Op) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment mode op)) JumpBranchSlt.importedConstraints := by
  cases mode
  · exact negative_native op
  · exact positive_native op
  · exact equal_native op

theorem accepted (mode : Mode) (op : Op) : Accepted (trace mode op) := by
  constructor
  · intro row member
    have eq : row = nativeRow mode op := by simpa [trace] using member
    subst row
    exact native_constraints mode op
  · intro row member
    have eq : row = nativeRow mode op := by simpa [trace] using member
    subst row
    cases mode <;> cases op <;> decide
  · change [(trace mode op).initial,(nativeRow mode op).finish].Perm
      [(trace mode op).terminal,(nativeRow mode op).start]
    have start : (nativeRow mode op).start = (trace mode op).initial := by cases mode <;> cases op <;> rfl
    have finish : (nativeRow mode op).finish = (trace mode op).terminal := by cases mode <;> cases op <;> rfl
    rw [start,finish]
    exact List.Perm.swap _ _ []
  · cases mode <;> cases op <;> decide +kernel

theorem public_inputs (mode : Mode) (op : Op) :
    ImageBoundary (trace mode op) (initial mode op) [.register 0,.register 1,.register 2] := by
  have zero : (Cell.register 0).read (initial mode op) = .ok (0 : BitVec 32) (initial mode op) := rfl
  have first : (Cell.register 1).read (initial mode op) =
      .ok (BitVec.ofNat 32 mode.left) (initial mode op) := by
    apply Reference.RiscV.Sail.read_register
    simp [initial,Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 2).read (initial mode op) =
      .ok (BitVec.ofNat 32 mode.right) (initial mode op) := by
    apply Reference.RiscV.Sail.read_register
    simp [initial,Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (initial mode op) =
      .ok (BitVec.ofNat 32 (4 * op.index)) (initial mode op) := by
    apply Reference.RiscV.Sail.read_register
    simp [initial]
  constructor
  · cases mode <;> decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,first,second]
    cases mode <;> rfl
  · rw [initialState,pc]
    cases op <;> rfl

theorem decoded (mode : Mode) (op : Op) : JumpBranchSlt.Decoded (trace mode op) setup := by
  intro row member
  have eq : row = nativeRow mode op := by simpa [trace] using member
  subst row
  cases op
  · refine ⟨⟨0,by decide⟩,?_⟩; cases mode <;> decide +kernel
  · refine ⟨⟨1,by decide⟩,?_⟩; cases mode <;> decide +kernel
  · refine ⟨⟨2,by decide⟩,?_⟩; cases mode <;> decide +kernel
  · refine ⟨⟨3,by decide⟩,?_⟩; cases mode <;> decide +kernel
  · refine ⟨⟨4,by decide⟩,?_⟩; cases mode <;> decide +kernel
  · refine ⟨⟨5,by decide⟩,?_⟩; cases mode <;> decide +kernel

/-- Eighteen initialized cases check both outcomes for each original branch,
    including equality and opposite signed/unsigned orderings. -/
theorem public_results (mode : Mode) (op : Op) :
    (assignment mode op 46).val = op.result mode ∧
    (assignment mode op 45).val = 1-op.result mode ∧
    (Word.mk (assignment mode op 38).val (assignment mode op 39).val).value = 0 := by
  have result := JumpBranchSlt.public_branches (program_image mode op) (public_inputs mode op)
    (accepted mode op) (decoded mode op) (nativeRow mode op) (by simp [trace]) (by cases mode <;> cases op <;> decide)
  convert result using 1 <;> cases mode <;> cases op <;> decide

def badEquality (i : Nat) : ZMod mersenne31Modulus :=
  if i = 29 ∨ i = 35 ∨ i = 46 then 0 else if i = 45 then 1
  else if i = 13 ∨ i = 42 ∨ i = 48 then 4 else assignment .equal .beq i

/-- The actual conditional table accepts a false equality flag and its false
    BEQ answer; the native inverse equation is what excludes this full row. -/
theorem bad_equality_table : conditionalControlTable.Contains #[]
    #v[JumpBranchSlt.controlBits badEquality,badEquality 11,badEquality 35] := by
  refine ⟨⟨0,by decide⟩,?_⟩
  decide +kernel

theorem bad_equality_rejected :
    ¬FlatOperation.ConstraintsHoldFlat (environment badEquality) JumpBranchSlt.importedConstraints := by
  intro holds
  have inverse := assertion_of_holds holds ⟨16,by rw [JumpBranchSlt.Proofs.constraint_count]; decide⟩
  exact (by decide +kernel :
    Expression.eval (environment badEquality)
      (FlatOperation.constraints JumpBranchSlt.importedConstraints)[16] ≠ 0) inverse

end Tests.Branches
