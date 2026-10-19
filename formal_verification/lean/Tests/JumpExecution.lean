import Tests.JumpTarget
import Airbender.Review.Trace.Families.JumpBranchSlt.JumpExecution

namespace Tests.JumpExecution
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail

def initial (indirect : Bool) (misa : BitVec 32) (security : BitVec 64) : State :=
  if indirect then
    { JumpTarget.before with regs := ((JumpTarget.before.regs.insert .misa misa).insert
        .cur_privilege .Machine).insert .mseccfg security }
  else { ControlHistory.before with regs := ControlHistory.before.regs.insert .misa misa }

def words (indirect : Bool) : Vector (BitVec 32) 3 :=
  if indirect then JumpLink.words else JumpBranchSlt.NativeSetup.words
def setup (indirect : Bool) : SparseDecoderSetup Unit :=
  if indirect then JumpLink.setup else JumpBranchSlt.NativeSetup.setup
def assignment (indirect : Bool) : Nat → ZMod mersenne31Modulus :=
  if indirect then JumpTarget.assignment else ControlHistory.assignment false
def nativeRow (indirect : Bool) : Row mersenne31Modulus JumpBranchSltFamily :=
  ⟨.jumpBranchSlt,assignment indirect⟩
def trace (indirect : Bool) : Data mersenne31Modulus JumpBranchSltFamily :=
  if indirect then JumpTarget.trace else ControlHistory.trace false

private theorem public_words (indirect : Bool) (misa : BitVec 32) (security : BitVec 64) (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (initial indirect misa security) =
      .ok (words indirect)[i.val] (initial indirect misa security) := by
  cases indirect <;> fin_cases i <;>
    simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      initial,words,ControlHistory.before,JumpTarget.before,JumpLink.before,
      JumpBranchSlt.NativeSetup.before,JumpBranchSlt.NativeSetup.words,JumpLink.words,
      Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 32768 in
private theorem jal_image (misa : BitVec 32) (security : BitVec 64) :
    JumpBranchSlt.sparseDecoderSetupImage (initial false misa security) 3 20 = some JumpBranchSlt.NativeSetup.setup := by
  have slots : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields (initial false misa security)) = some JumpBranchSlt.NativeSetup.setup.slots := by
    simp only [List.mapM_cons, List.mapM_nil, programSlotWith,
      show (Cell.ram 0).read (initial false misa security) = .ok (0xffdff0ef : BitVec 32) (initial false misa security) from public_words false misa security ⟨0, by decide⟩,
      show (Cell.ram 4).read (initial false misa security) = .ok (0xc0001073 : BitVec 32) (initial false misa security) from public_words false misa security ⟨1, by decide⟩,
      show (Cell.ram 8).read (initial false misa security) = .ok (0xfff0b013 : BitVec 32) (initial false misa security) from public_words false misa security ⟨2, by decide⟩,
      bind, Option.bind]
    cbv
  change (([0,4,8] : List (BitVec 32)).mapM (programSlotWith JumpBranchSlt.decoderFields (initial false misa security))).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048573)) = some JumpBranchSlt.NativeSetup.setup
  rw [slots]
  rfl

set_option maxRecDepth 32768 in
private theorem jalr_image (misa : BitVec 32) (security : BitVec 64) :
    JumpBranchSlt.sparseDecoderSetupImage (initial true misa security) 3 20 = some JumpLink.setup := by
  have slots : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields (initial true misa security)) = some JumpLink.setup.slots := by
    simp only [List.mapM_cons, List.mapM_nil, programSlotWith,
      show (Cell.ram 0).read (initial true misa security) = .ok (0xffdff0ef : BitVec 32) (initial true misa security) from public_words true misa security ⟨0, by decide⟩,
      show (Cell.ram 4).read (initial true misa security) = .ok (0x008080e7 : BitVec 32) (initial true misa security) from public_words true misa security ⟨1, by decide⟩,
      show (Cell.ram 8).read (initial true misa security) = .ok (0x0080006f : BitVec 32) (initial true misa security) from public_words true misa security ⟨2, by decide⟩,
      bind, Option.bind]
    cbv
  change (([0,4,8] : List (BitVec 32)).mapM (programSlotWith JumpBranchSlt.decoderFields (initial true misa security))).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048573)) = some JumpLink.setup
  rw [slots]
  rfl

/-- Both existing public byte images are unchanged by actual CSR initialization. -/
theorem program_image (indirect : Bool) (misa : BitVec 32) (security : BitVec 64) :
    JumpBranchSlt.sparseDecoderSetupImage (initial indirect misa security) 3 20 = some (setup indirect) := by
  cases indirect
  · exact jal_image misa security
  · exact jalr_image misa security

theorem public_inputs (indirect : Bool) (misa : BitVec 32) (security : BitVec 64) :
    ImageBoundary (trace indirect) (initial indirect misa security) [.register 0,.register 1] := by
  have zero : (Cell.register 0).read (initial indirect misa security) =
      .ok (0 : BitVec 32) (initial indirect misa security) := rfl
  have old : (Cell.register 1).read (initial indirect misa security) =
      .ok (if indirect then (257 : BitVec 32) else 123) (initial indirect misa security) := by
    apply read_register
    cases indirect <;> simp [initial,ControlHistory.before,JumpTarget.before,Std.ExtDHashMap.get?_insert]
  have pc : run (SailRV32.Functions.get_arch_pc ()) (initial indirect misa security) =
      .ok (if indirect then (4 : BitVec 32) else 0) (initial indirect misa security) := by
    apply read_register
    cases indirect <;> simp [initial,ControlHistory.before,JumpTarget.before,Std.ExtDHashMap.get?_insert]
  constructor
  · cases indirect <;> decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,old]
    cases indirect <;> rfl
  · rw [initialState,pc]
    cases indirect <;> rfl

/-- Execute the unchanged exported negative JAL and logical aliasing JALR from
    actual public states. The same constructed after-state receives the native
    link and original retirement; no expected after-state is supplied. -/
theorem initialized_execution (indirect : Bool) (misa : BitVec 32) (security : BitVec 64)
    (disabled : SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    ∃ entry ∈ (setup indirect).program, ∃ clause after,
      entry.SourceWith (initial indirect misa security) JumpBranchSlt.decoderFields ∧
      JumpBranchSlt.decoderQuery (assignment indirect) = entry.query ∧
      registerClause entry.instruction = some clause ∧
      run (normalStep clause) (initial indirect misa security) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (if indirect then (264 : BitVec 32) else 0xfffffffc)) ∧
      run (SailRV32.Functions.wX_bits (.Regidx 1) (if indirect then (8 : BitVec 32) else 4))
        (initial indirect misa security) = .ok () after := by
  have aligned : ∀ cell ∈ [Cell.register 0,.register 1], cell.Aligned := by
    intro cell member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> simp [Cell.Aligned]
  have isa : ∃ value, (initial indirect misa security).regs.get? .misa = some value := by
    refine ⟨misa,?_⟩
    cases indirect <;> simp [initial,Std.ExtDHashMap.get?_insert]
  have configuration : (∃ row ∈ (trace indirect).rows, (row.assignment 12).val = 2) →
      (initial indirect misa security).regs.get? .cur_privilege = some .Machine ∧
      ∃ value, (initial indirect misa security).regs.get? .mseccfg = some value ∧
        SailRV32.Functions._get_Seccfg_MLPE value = 0 := by
    rintro ⟨row,present,mask⟩
    cases indirect
    · have same : row = ControlHistory.nativeRow false := by simpa [trace,ControlHistory.trace] using present
      subst row
      exact False.elim ((by decide : (ControlHistory.assignment false 12).val ≠ 2) mask)
    · exact ⟨by simp [initial,Std.ExtDHashMap.get?_insert],security,by simp [initial],disabled⟩
  have accepted : Accepted (trace indirect) := by
    cases indirect
    · exact ControlHistory.accepted
    · exact JumpTarget.accepted
  have decoded : JumpBranchSlt.Decoded (trace indirect) (setup indirect) := by
    cases indirect
    · exact ControlValues.decoded
    · exact JumpTarget.decoded
  obtain ⟨history,rows,after,_,permutation,_,_,_,segments⟩ :=
    JumpBranchSlt.public_jump_execution (program_image indirect misa security)
      (public_inputs indirect misa security) accepted decoded isa configuration aligned
  have singleton : rows = [nativeRow indirect] := by
    apply List.perm_singleton.mp
    cases indirect <;> simpa [trace,JumpTarget.trace,ControlHistory.trace,nativeRow,assignment,
      JumpTarget.nativeRow,ControlHistory.nativeRow] using permutation
  obtain ⟨entry,member,rowBefore,rowAfter,clause,source,query,earlier,current,later,matched,retired⟩ :=
    segments [] (nativeRow indirect) [] singleton (by cases indirect <;> decide)
  change SailHistory _ [] (initial indirect misa security) rowBefore at earlier
  change SailHistory _ [] rowAfter after at later
  cases earlier
  cases later
  have inputPC : (Word.mk (assignment indirect 0).val (assignment indirect 1).val).toBitVec =
      if indirect then (4 : BitVec 32) else 0 := by cases indirect <;> decide
  have outputPC : (Word.mk (assignment indirect 13).val (assignment indirect 14).val).toBitVec =
      if indirect then (264 : BitVec 32) else 0xfffffffc := by cases indirect <;> decide
  have pc : run (SailRV32.Functions.get_arch_pc ()) (initial indirect misa security) =
      .ok (if indirect then (4 : BitVec 32) else 0) (initial indirect misa security) := by
    apply read_register
    cases indirect <;> simp [initial,ControlHistory.before,JumpTarget.before,Std.ExtDHashMap.get?_insert]
  change run (normalStep clause)
    (retiredState (initial indirect misa security) (Word.mk (assignment indirect 0).val (assignment indirect 1).val).toBitVec) =
    .ok SailRV32.Functions.RETIRE_SUCCESS
      (retiredState after (Word.mk (assignment indirect 13).val (assignment indirect 14).val).toBitVec) at retired
  rw [inputPC,outputPC,Trace.Proofs.normal_step_rebased pc clause] at retired
  have index := (Trace.Proofs.native_query_indices (by decide : limbBase < mersenne31Modulus) query).2.2
  change (assignment indirect 7).val = entry.data.rd.toNat at index
  have one : (assignment indirect 7).val = 1 := by cases indirect <;> decide
  have rd : entry.data.rd = 1 := BitVec.eq_of_toNat_eq (by simpa [one] using index.symm)
  have written := JumpBranchSlt.Proofs.history_register_write (by decide) (trace indirect).memoryEpoch current query
  rw [rd] at written
  have nativeWrite : run (SailRV32.Functions.wX_bits (.Regidx 1)
      (Word.mk (assignment indirect 38).val (assignment indirect 39).val).toBitVec)
      (initial indirect misa security) = .ok () after := by
    simpa [memoryWord,MemoryPort.writeCode,WordColumns.code,WordColumns.evaluate,
      JumpBranchSlt.importedConstraintsMemoryPorts,Nat.unpair_pair] using written
  have link : (Word.mk (assignment indirect 38).val (assignment indirect 39).val).toBitVec =
      if indirect then (8 : BitVec 32) else 4 := by cases indirect <;> decide
  rw [link] at nativeWrite
  exact ⟨entry,member,clause,after,source,query,matched,retired,nativeWrite⟩

/-- The JAL case succeeds with neither privilege nor security CSR initialized. -/
theorem jal_no_landing_profile (misa : BitVec 32) (security : BitVec 64) :
    (initial false misa security).regs.get? .cur_privilege = none ∧
      (initial false misa security).regs.get? .mseccfg = none := by
  simp [initial,ControlHistory.before,Std.ExtDHashMap.get?_insert]

/-- The prior partial JALR state cannot supply its original privilege read. -/
theorem missing_privilege_read :
    ¬∃ value, run (SailRV32.readReg .cur_privilege) JumpTarget.before = .ok value JumpTarget.before := by
  rintro ⟨value,read⟩
  have present := read_register_iff.mp read
  simp [JumpTarget.before,Std.ExtDHashMap.get?_insert] at present

end Tests.JumpExecution
