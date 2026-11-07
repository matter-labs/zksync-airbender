import Airbender.Review.Trace.Families.ReducedMachine.SupportedExecution

namespace Tests.NativeReducedSupportedJumps
open Airbender Arithmetic Trace ReducedMachine Native
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Independent original public bytes, not complete accepted native rows.
private def before (misa : BitVec 32) : State :=
  { (default : State) with
    regs := (((Std.ExtDHashMap.emptyWithCapacity.insert .misa misa).insert .PC (0 : BitVec 32)).insert .cur_privilege .Machine).insert .mseccfg (0 : BitVec 64)
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 0x6f |>.insert 1 0 |>.insert 2 0x80 |>.insert 3 0
      |>.insert 4 0xb3 |>.insert 5 0x81 |>.insert 6 0x20 |>.insert 7 0
      |>.insert 8 0xe7 |>.insert 9 0x80 |>.insert 10 0x80 |>.insert 11 0) }
private def words : Vector (BitVec 32) 3 := #v[0x0080006f,0x002081b3,0x008080e7]
private def instructions : Vector SailRV32.instruction 3 :=
  #v[.JAL (8,.Regidx 0),.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.ADD),
     .JALR (8,.Regidx 1,.Regidx 1)]
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

/-- Original jump and arithmetic bytes coexist in one complete public setup,
    retaining original x0/direct target and aliased JALR around the PC4 ADD slot. -/
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

/-- Every jump/arithmetic slot has original byte and stateful Sail decoder
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

/-- Native masks/tags keep original negative offsets, x0 and raw operands. -/
theorem original_jump_fields :
    supportedDecoderFields (.JAL (0x1ffffc,.Regidx 0)) =
      some ⟨.inr (.inr (.inr (.inr (.inr true)))),0,0,0,⟨65532,65535⟩,33025,7⟩ ∧
    supportedDecoderFields (.JALR (4095,.Regidx 1,.Regidx 0)) =
      some ⟨.inr (.inr (.inr (.inr (.inr false)))),1,0,0,⟨65535,65535⟩,257,0⟩ := ⟨rfl,rfl⟩

/-- Every readable misa value is allowed; actual local reads derive from history. -/
theorem unrestricted_initial_configuration (misa : BitVec 32) : SupportedISA setup (before misa) := by
  constructor
  · intro _
    exact ⟨misa,by simp [before,Std.ExtDHashMap.get?_insert]⟩
  · intro _
    exact ⟨by simp [before,Std.ExtDHashMap.get?_insert],0,by simp [before],by decide +kernel⟩

/-- An original jump-containing program cannot fabricate a missing misa read. -/
theorem missing_misa_rejected :
    ¬ SupportedISA setup { (before 0) with regs := Std.ExtDHashMap.emptyWithCapacity } := by
  intro ready
  let entry : SupportedProgramEntry := ⟨0,words[0],instructions[0],
    ⟨.inr (.inr (.inr (.inr (.inr true)))),0,0,0,⟨8,0⟩,33025,0⟩⟩
  have slot : some entry ∈ setup.slots := List.getElem_mem (l := setup.slots) (n := 0) (by decide)
  have member : entry ∈ setup.program := List.mem_filterMap.mpr ⟨some entry,slot,rfl⟩
  obtain ⟨value,read⟩ := ready.1 ⟨entry,member,by change True; trivial⟩
  simp at read

/-- Original JALR landing-pad CSR participation is retained after mixed transport. -/
theorem missing_security_rejected :
    ¬ SupportedISA setup { (before 0) with regs :=
      (Std.ExtDHashMap.emptyWithCapacity.insert .misa (0 : BitVec 32)).insert .cur_privilege .Machine } := by
  intro ready
  let entry : SupportedProgramEntry := ⟨8,words[2],instructions[2],
    ⟨.inr (.inr (.inr (.inr (.inr false)))),1,0,1,⟨8,0⟩,257,0⟩⟩
  have slot : some entry ∈ setup.slots := List.getElem_mem (l := setup.slots) (n := 2) (by decide)
  have member : entry ∈ setup.program := List.mem_filterMap.mpr ⟨some entry,slot,rfl⟩
  obtain ⟨_,security,read,_⟩ := ready.2 ⟨entry,member,_,rfl⟩
  simp [Std.ExtDHashMap.get?_insert] at read

end Tests.NativeReducedSupportedJumps
