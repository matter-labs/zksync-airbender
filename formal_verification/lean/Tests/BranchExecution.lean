import Tests.Branches
import Airbender.Review.Trace.Families.JumpBranchSlt.BranchExecution

namespace Tests.BranchExecution
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
open Tests.Branches

/-- Preserve all eighteen native fixtures and public bytes. Supply one actual
    public CSR entry, with arbitrary value, needed by the original taken clause. -/
def publicInitial (misa : BitVec 32) (mode : Mode) (op : Op) : State :=
  { initial mode op with regs := (initial mode op).regs.insert .misa misa }

set_option maxRecDepth 65536 in
theorem program_image (misa : BitVec 32) (mode : Mode) (op : Op) :
    JumpBranchSlt.sparseDecoderSetupImage (publicInitial misa mode op) 6 20 = some setup := by
  have public_words (i : Fin 6) : (Cell.ram (BitVec.ofNat 32 (4 * (i.val)))).read (publicInitial misa mode op) =
      .ok words[i.val] (publicInitial misa mode op) := by
    fin_cases i <;> simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
      EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
      publicInitial,initial,before,words,Std.ExtHashMap.getElem_insert]
  have slots : ([0,4,8,12,16,20] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields (publicInitial misa mode op)) = some setup.slots := by
    simp only [List.mapM_cons,List.mapM_nil,programSlotWith,
      show (Cell.ram 0).read (publicInitial misa mode op) = .ok (0x208463 : BitVec 32) (publicInitial misa mode op) from public_words ⟨0,by decide⟩,
      show (Cell.ram 4).read (publicInitial misa mode op) = .ok (0x209463 : BitVec 32) (publicInitial misa mode op) from public_words ⟨1,by decide⟩,
      show (Cell.ram 8).read (publicInitial misa mode op) = .ok (0x20c463 : BitVec 32) (publicInitial misa mode op) from public_words ⟨2,by decide⟩,
      show (Cell.ram 12).read (publicInitial misa mode op) = .ok (0x20d463 : BitVec 32) (publicInitial misa mode op) from public_words ⟨3,by decide⟩,
      show (Cell.ram 16).read (publicInitial misa mode op) = .ok (0x20e463 : BitVec 32) (publicInitial misa mode op) from public_words ⟨4,by decide⟩,
      show (Cell.ram 20).read (publicInitial misa mode op) = .ok (0x20f463 : BitVec 32) (publicInitial misa mode op) from public_words ⟨5,by decide⟩,bind,Option.bind]
    cbv
  change (([0,4,8,12,16,20] : List (BitVec 32)).mapM
    (programSlotWith JumpBranchSlt.decoderFields (publicInitial misa mode op))).bind
      (fun entries => some (SparseDecoderSetup.mk entries 1048570)) = some setup
  rw [slots]
  rfl

theorem public_inputs (misa : BitVec 32) (mode : Mode) (op : Op) :
    ImageBoundary (trace mode op) (publicInitial misa mode op) [.register 0,.register 1,.register 2] := by
  have zero : (Cell.register 0).read (publicInitial misa mode op) = .ok (0 : BitVec 32) (publicInitial misa mode op) := rfl
  have first : (Cell.register 1).read (publicInitial misa mode op) =
      .ok (BitVec.ofNat 32 mode.left) (publicInitial misa mode op) := by
    apply Reference.RiscV.Sail.read_register
    simp [publicInitial,initial,Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 2).read (publicInitial misa mode op) =
      .ok (BitVec.ofNat 32 mode.right) (publicInitial misa mode op) := by
    apply Reference.RiscV.Sail.read_register
    simp [publicInitial,initial,Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (publicInitial misa mode op) =
      .ok (BitVec.ofNat 32 (4 * op.index)) (publicInitial misa mode op) := by
    apply Reference.RiscV.Sail.read_register
    simp [publicInitial,initial,Std.ExtDHashMap.get?_insert]
  constructor
  · cases mode <;> decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,first,second]
    cases mode <;> rfl
  · rw [initialState,pc]
    cases op <;> rfl

/-- All eighteen initialized native cases execute their original public-decoded
    branch from the actual public state. The real discarded destination write
    derives full data-state stuttering; retirement chooses the checked target.
    No native row, read, result, PC or after-state is replaced. -/
theorem initialized_execution (misa : BitVec 32) (mode : Mode) (op : Op) :
    ∃ entry ∈ setup.program, ∃ clause,
      entry.SourceWith (publicInitial misa mode op) JumpBranchSlt.decoderFields ∧
      JumpBranchSlt.decoderQuery (assignment mode op) = entry.query ∧
      registerClause entry.instruction = some clause ∧
      run (normalStep clause) (publicInitial misa mode op) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState (publicInitial misa mode op) (BitVec.ofNat 32 (op.finish mode))) := by
  have aligned : ∀ cell ∈ [Cell.register 0,.register 1,.register 2], cell.Aligned := by
    intro cell member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [Cell.Aligned]
  have isa : ∃ value, (publicInitial misa mode op).regs.get? .misa = some value :=
    ⟨misa,by simp [publicInitial]⟩
  obtain ⟨history,rows,after,_,permutation,_,_,_,segments⟩ :=
    JumpBranchSlt.public_branch_execution (program_image misa mode op) (public_inputs misa mode op)
      (accepted mode op) (decoded mode op) isa aligned
  have singleton : rows = [nativeRow mode op] :=
    List.perm_singleton.mp (by simpa only [trace] using permutation)
  obtain ⟨entry,member,rowBefore,rowAfter,clause,source,query,earlier,current,later,matched,retired⟩ :=
    segments [] (nativeRow mode op) [] singleton (by cases mode <;> cases op <;> decide)
  change SailHistory _ [] (publicInitial misa mode op) rowBefore at earlier
  change SailHistory _ [] rowAfter after at later
  cases earlier
  cases later
  have inputPC : (Word.mk (assignment mode op 0).val (assignment mode op 1).val).toBitVec =
      BitVec.ofNat 32 (4 * op.index) := by cases mode <;> cases op <;> decide
  have outputPC : (Word.mk (assignment mode op 13).val (assignment mode op 14).val).toBitVec =
      BitVec.ofNat 32 (op.finish mode) := by cases mode <;> cases op <;> decide
  have pc : run (SailRV32.Functions.get_arch_pc ()) (publicInitial misa mode op) =
      .ok (BitVec.ofNat 32 (4 * op.index)) (publicInitial misa mode op) := by
    apply read_register
    simp [publicInitial,initial,Std.ExtDHashMap.get?_insert]
  change run (normalStep clause)
    (retiredState (publicInitial misa mode op) (Word.mk (assignment mode op 0).val (assignment mode op 1).val).toBitVec) =
    .ok SailRV32.Functions.RETIRE_SUCCESS
      (retiredState after (Word.mk (assignment mode op 13).val (assignment mode op 14).val).toBitVec) at retired
  have rd := (Trace.Proofs.native_query_indices (by decide : limbBase < mersenne31Modulus) query).2.2
  change 0 = entry.data.rd.toNat at rd
  have zero : entry.data.rd = 0 := BitVec.eq_of_toNat_eq (by simpa using rd.symm)
  have written := JumpBranchSlt.Proofs.history_register_write (by decide) (trace mode op).memoryEpoch current query
  rw [zero] at written
  change run (SailRV32.Functions.wX_bits zeroRegister _) (publicInitial misa mode op) = .ok () after at written
  rw [write_zero] at written
  have same : publicInitial misa mode op = after := (EStateM.Result.ok.inj written).2
  rw [← same,inputPC,outputPC,Trace.Proofs.normal_step_rebased pc clause] at retired
  exact ⟨entry,member,clause,source,query,matched,retired⟩

/-- Prior native fixtures leave misa absent; successful original taken-branch
    execution therefore requires the explicit real public CSR entry above. -/
theorem missing_isa (mode : Mode) (op : Op) :
    ¬∃ value, (initial mode op).regs.get? .misa = some value := by
  simp [initial,Std.ExtDHashMap.get?_insert]

/-- The actual original CSR accessor cannot return successfully on the prior
    partial public state. The configured executions above supply a real entry. -/
theorem missing_isa_read (mode : Mode) (op : Op) :
    ¬∃ value, run (SailRV32.readReg .misa) (initial mode op) = .ok value (initial mode op) := by
  rintro ⟨value,read⟩
  exact missing_isa mode op ⟨value,read_register_iff.mp read⟩

end Tests.BranchExecution
