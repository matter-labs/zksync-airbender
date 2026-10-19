import Tests.ControlExecution
import Airbender.Review.Helpers.Properties

namespace Tests.ControlSequence
open Airbender Trace Verification Arithmetic Reference.RiscV.Sail Reference.Sail

/-- Original JAL x1,+4 followed by aliasing JALR x1,0(x1). JALR must read the
    preceding link four rather than the public old x1=124. -/
def first (i : Nat) : ZMod mersenne31Modulus :=
  if i = 9 ∨ i = 13 ∨ i = 42 ∨ i = 48 ∨ i = 54 then 4
  else if i = 40 then 124 else JumpControl.assignment i

def second (stale : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 2 ∨ i = 57 then 8 else if i = 15 then 12
  else if i = 9 then 0 else if i = 51 then 6 else if i = 54 then 5
  else if i = 22 ∨ i = 40 ∨ i = 13 ∨ i = 42 ∨ i = 48 then if stale then 124 else 4
  else JumpLink.jalr i

def nativeRow (indirect stale : Bool) : Row mersenne31Modulus JumpBranchSltFamily :=
  ⟨.jumpBranchSlt,if indirect then second stale else first⟩
private def cell (register time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair register 0),(time,0),Nat.pair value 0⟩
def trace (stale : Bool) : Data mersenne31Modulus JumpBranchSltFamily where
  rows := [nativeRow true stale,nativeRow false stale]
  rom := ()
  initial := ⟨(0,0),(4,0)⟩
  terminal := ⟨(if stale then 124 else 4,0),(12,0)⟩
  initialMemory := [cell 0 0 0,cell 1 0 124]
  terminalMemory := [cell 0 9 0,cell 1 10 8]

def words : Vector (BitVec 32) 2 := #v[0x004000ef,0x000080e7]
def before : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (124 : BitVec 32) |>.insert .PC (0 : BitVec 32)
      |>.insert .misa (0 : BitVec 32) |>.insert .cur_privilege .Machine |>.insert .mseccfg (0 : BitVec 64))
    mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 0xef |>.insert 1 0x00 |>.insert 2 0x40 |>.insert 3 0x00
      |>.insert 4 0xe7 |>.insert 5 0x80 |>.insert 6 0x00 |>.insert 7 0x00) }
def setup : SparseDecoderSetup Unit :=
  ⟨[some ⟨0,0x004000ef,.JAL (4,.Regidx 1),⟨(),0,0,1,⟨4,0⟩,1,0⟩⟩,
    some ⟨4,0x000080e7,.JALR (0,.Regidx 1,.Regidx 1),⟨(),1,0,1,⟨0,0⟩,2,0⟩⟩],1048574⟩

private theorem public_words (i : Fin 2) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before = .ok words[i.val] before := by
  fin_cases i <;> simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
    before,words,Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 32768 in
theorem program_image : JumpBranchSlt.sparseDecoderSetupImage before 2 20 = some setup := by
  have slots : ([0,4] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields before) = some setup.slots := by
    simp only [List.mapM_cons,List.mapM_nil,programSlotWith,
      show (Cell.ram 0).read before = .ok (0x004000ef : BitVec 32) before from public_words ⟨0,by decide⟩,
      show (Cell.ram 4).read before = .ok (0x000080e7 : BitVec 32) before from public_words ⟨1,by decide⟩,
      bind,Option.bind]
    cbv
  change (([0,4] : List (BitVec 32)).mapM (programSlotWith JumpBranchSlt.decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048574)) = some setup
  rw [slots]
  rfl

/-- Both the real and stale variants satisfy every native equation/query.
    Their distinction is enforced by actual logical native memory matching. -/
theorem native_constraints (indirect stale : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (if indirect then second stale else first))
      JumpBranchSlt.importedConstraints := by
  cases indirect <;> cases stale <;>
    simp [JumpBranchSlt.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,first,second,JumpLink.jalr,JumpControl.assignment]
  all_goals
    repeat' apply And.intro
    all_goals first | (apply range16_contains; decide) | (apply timestamp19_contains; decide) | try decide
    all_goals
      simp only [Lookup.Contains,fixed3,Table.toRaw,conditionalControlTable,jumpCleanupTable,
        Table.fromStatic,StaticTable.toTable,ProvableType.fromElements,Expression.eval,
        Vector.map_mk,List.map_toArray,List.map_cons,List.map_nil,first,second,JumpLink.jalr,JumpControl.assignment]
      solve
      | refine ⟨⟨0,by decide⟩,?_⟩
        norm_num [conditionalControlRow,controlFlag]
      | refine ⟨⟨4,by decide⟩,?_⟩
        norm_num [jumpCleanupRow]
      | refine ⟨⟨124,by decide⟩,?_⟩
        norm_num [jumpCleanupRow]

/-- Both variants satisfy actual native state matching; only the stale
    memory read distinguishes them. Rows deliberately arrive newest first. -/
theorem state_matching (stale : Bool) :
    ((trace stale).initial :: (trace stale).rows.map Row.finish).Perm
      ((trace stale).terminal :: (trace stale).rows.map Row.start) := by
  change [(trace stale).initial,(nativeRow true stale).finish,(nativeRow false stale).finish].Perm
    [(trace stale).terminal,(nativeRow true stale).start,(nativeRow false stale).start]
  have start : (nativeRow false stale).start = (trace stale).initial := by cases stale <;> rfl
  have middle : (nativeRow false stale).finish = (nativeRow true stale).start := by cases stale <;> rfl
  have finish : (nativeRow true stale).finish = (trace stale).terminal := by cases stale <;> rfl
  rw [start,middle,finish]
  exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))

theorem accepted : Accepted (trace false) := by
  constructor
  · intro row present
    simp only [trace,List.mem_cons,List.mem_nil_iff,or_false] at present
    rcases present with rfl | rfl
    · exact native_constraints true false
    · exact native_constraints false false
  · intro row present
    simp only [trace,List.mem_cons,List.mem_nil_iff,or_false] at present
    rcases present with rfl | rfl <;> decide
  · exact state_matching false
  · change ([cell 0 0 0,cell 1 0 124,cell 1 8 4,cell 0 9 0,cell 1 10 8,cell 0 4 0,cell 0 5 0,cell 1 6 4]).Perm
      [cell 0 9 0,cell 1 10 8,cell 1 6 4,cell 0 5 0,cell 1 8 4,cell 0 0 0,cell 0 4 0,cell 1 0 124]
    decide +kernel

theorem public_inputs : ImageBoundary (trace false) before [.register 0,.register 1] := by
  have zero : (Cell.register 0).read before = .ok (0 : BitVec 32) before := rfl
  have old : (Cell.register 1).read before = .ok (124 : BitVec 32) before := by
    apply read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok (0 : BitVec 32) before := by
    apply read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  constructor
  · decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,old]
    rfl
  · rw [initialState,pc]
    rfl

theorem decoded (stale : Bool) : JumpBranchSlt.Decoded (trace stale) setup := by
  intro row present
  simp only [trace,List.mem_cons,List.mem_nil_iff,or_false] at present
  rcases present with rfl | rfl
  · refine ⟨⟨1,by decide⟩,?_⟩
    cases stale <;> decide +kernel
  · refine ⟨⟨0,by decide⟩,?_⟩
    cases stale <;> decide +kernel

/-- Actual row order, the intermediate link four, both original fetches and
    the final state all come from the public theorem and native matching. -/
theorem execution : Realizes (StepWith JumpBranchSlt.decoderFields registerClause setup.program)
    (trace false) before [.register 0,.register 1] := by
  have aligned : ∀ cell ∈ [Cell.register 0,.register 1], cell.Aligned := by
    intro cell member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> simp [Cell.Aligned]
  exact (JumpBranchSlt.public_execution program_image public_inputs accepted (decoded false)
    ⟨0,by simp [before,Std.ExtDHashMap.get?_insert]⟩
    (fun _ => ⟨by simp [before,Std.ExtDHashMap.get?_insert],0,by simp [before],by decide⟩) aligned).2

/-- The stale source retains valid local native constraints and public decoder
    membership, but cannot consume JAL's actual link-four memory token. -/
theorem stale_rejected : ¬Accepted (trace true) := by
  intro h
  have wrong := h.memory.count_eq (cell 1 6 4)
  revert wrong
  decide +kernel

/-- Actual terminal x1=8 and PC four are obtained from the composed execution;
    no intermediate state/read or final-value premise is supplied. -/
theorem final_values : ∃ after,
    Relation.ReflTransGen (StepWith JumpBranchSlt.decoderFields registerClause setup.program) before after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok (4 : BitVec 32) after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 1)) after = .ok (8 : BitVec 32) after := by
  obtain ⟨after,steps,pc,reads⟩ := execution
  obtain ⟨found,member,address,read⟩ := reads (cell 1 10 8) (by simp [trace])
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl
  · have impossible : (Cell.register 0).addressCode ≠ (cell 1 10 8).address := by decide
    exact False.elim (impossible address)
  · have word : (id (cell 1 10 8)).word.toBitVec = (8 : BitVec 32) := by decide +kernel
    rw [word] at read
    exact ⟨after,steps,pc,read⟩

end Tests.ControlSequence
