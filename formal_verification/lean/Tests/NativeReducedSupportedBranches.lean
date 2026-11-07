import Airbender.Review.Trace.Families.ReducedMachine.SupportedExecution

namespace Tests.NativeReducedSupportedBranches
open Airbender Arithmetic Trace ReducedMachine Native
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Independent original public bytes. These are not full117-equation native rows.
private def before (misa : BitVec 32) : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity.insert .misa misa).insert .PC (0 : BitVec 32)
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 0x63 |>.insert 1 0x84 |>.insert 2 0x20 |>.insert 3 0
      |>.insert 4 0x33 |>.insert 5 0 |>.insert 6 0 |>.insert 7 0
      |>.insert 8 0xb3 |>.insert 9 0x81 |>.insert 10 0x20 |>.insert 11 0) }
private def words : Vector (BitVec 32) 3 := #v[0x00208463,0x00000033,0x002081b3]
private def instructions : Vector SailRV32.instruction 3 :=
  #v[.BTYPE (8,.Regidx 2,.Regidx 1,.BEQ),.RTYPE (.Regidx 0,.Regidx 0,.Regidx 0,.ADD),
     .RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.ADD)]
private def slots : List (Option SupportedProgramEntry) :=
  (List.finRange 3).map fun i => (supportedDecoderFields instructions[i]).map fun data =>
    ⟨BitVec.ofNat 32 (4 * i.val),words[i],instructions[i],data⟩
private def setup : SparseDecoderSetup SupportedMode := ⟨slots,1⟩

private theorem public_words (misa : BitVec 32) (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (before misa) = .ok words[i] (before misa) := by
  fin_cases i <;> simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
    before,words,Std.ExtHashMap.getElem_insert]

private theorem public_slot (misa : BitVec 32) (i : Fin 3) :
    programSlotRunWith supportedDecoderFields (before misa) (BitVec.ofNat 32 (4 * i.val)) =
      some ((supportedDecoderFields instructions[i]).map fun data =>
        (⟨BitVec.ofNat 32 (4 * i.val),words[i],instructions[i],data⟩ : SupportedProgramEntry)) := by
  simp only [programSlotRunWith,public_words,bind,Option.bind]
  fin_cases i <;> rfl

/-- Original branch and arithmetic bytes coexist in one complete public setup,
    retaining native branch mask70, offset8 and the PC4/PC8 arithmetic slots. -/
theorem mixed_public_image (misa : BitVec 32) :
    supportedDecoderSetupImage (before misa) 3 2 = some setup := by
  have fetched : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotRunWith supportedDecoderFields (before misa)) = some slots := by
    simp only [List.mapM_cons,List.mapM_nil,
      show programSlotRunWith supportedDecoderFields (before misa) 0 = _ from public_slot misa 0,
      show programSlotRunWith supportedDecoderFields (before misa) 4 = _ from public_slot misa 1,
      show programSlotRunWith supportedDecoderFields (before misa) 8 = _ from public_slot misa 2,
      bind,Option.bind,pure]
    rfl
  change (([0,4,8] : List (BitVec 32)).mapM
    (programSlotRunWith supportedDecoderFields (before misa))).bind
      (fun entries => some (SparseDecoderSetup.mk entries 1)) = some setup
  rw [fetched]
  rfl

/-- Every branch/arithmetic slot has original byte and stateful Sail decoder
    evidence; expected profiles and query fields are not assumed publicly. -/
theorem original_mixed_sources (misa : BitVec 32) (i : Fin 3) :
    ∃ entry, setup.slots[i.val]? = some (some entry) ∧
      entry.SourceWith (before misa) supportedDecoderFields := by
  have filled : ∃ entry, setup.slots[i.val]? = some (some entry) := by
    fin_cases i <;> exact ⟨_,rfl⟩
  obtain ⟨entry,found⟩ := filled
  have member : entry ∈ setup.program := List.mem_filterMap.mpr
    ⟨some entry,List.mem_of_getElem? found,rfl⟩
  exact ⟨entry,found,(Trace.Proofs.run_sparse_setup_sources (mixed_public_image misa) member).1⟩

/-- Original branches, raw x0 aliases and negative offset survive the common
    projection with the exact native dummy destination/zero flag conventions. -/
theorem original_branch_fields (op : BranchMode) :
    supportedDecoderFields (.BTYPE (8190,.Regidx 0,.Regidx 0,op)) =
      some ⟨.inr (.inr (.inr (.inr op))),0,0,0,⟨65534,65535⟩,70,branchFunct3 op⟩ := by
  cases op <;> rfl

/-- A program with branches accepts any readable initial misa value. Each
    actual row's read is later derived through the common history. -/
theorem unrestricted_initial_isa (misa : BitVec 32) : SupportedISA setup (before misa) := by
  intro _
  exact ⟨misa,by simp [before,Std.ExtDHashMap.get?_insert]⟩

/-- This is a meaningful public configuration condition: a branch-containing
    program cannot silently assume an absent initial CSR becomes readable. -/
theorem missing_isa_rejected :
    ¬ SupportedISA setup { (before 0) with regs := Std.ExtDHashMap.emptyWithCapacity } := by
  intro ready
  let branch : SupportedProgramEntry := ⟨0,words[0],instructions[0],
      ⟨.inr (.inr (.inr (.inr .BEQ))),1,2,0,⟨8,0⟩,70,0⟩⟩
  have slot : some branch ∈ setup.slots := List.getElem_mem (l := setup.slots) (n := 0) (by decide)
  have member : branch ∈ setup.program := List.mem_filterMap.mpr ⟨some branch,slot,rfl⟩
  obtain ⟨value,read⟩ := ready ⟨_,member,_,rfl⟩
  simp at read

/-- CSR-free ordinary programs keep their previous scope. The condition is
    vacuous from the actual program constructors, not from a supplied row read. -/
theorem ordinary_no_isa (initial : State) :
    SupportedISA (⟨[some ⟨0,0x002081b3,instructions[2],
      ⟨.inr (.inl .add),1,2,3,⟨0,0⟩,11,0⟩⟩],1⟩ : SparseDecoderSetup SupportedMode) initial := by
  rintro ⟨entry,member,args,shape⟩
  have same : entry = (⟨0,0x002081b3,instructions[2],
      ⟨.inr (.inl .add),1,2,3,⟨0,0⟩,11,0⟩⟩ : SupportedProgramEntry) := by
    simpa [SparseDecoderSetup.program] using member
  subst entry
  cases shape

end Tests.NativeReducedSupportedBranches
