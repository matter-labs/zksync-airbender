import Airbender.Review.Trace.Families.ReducedMachine.BranchResults
import Airbender.Review.Trace.Families.ReducedMachine.BranchDecoder
import Airbender.Review.Trace.Families.ReducedMachine.BranchValues
import Tests.Branches

namespace Tests.NativeReducedBranchDecoder
open Airbender Arithmetic Trace ReducedMachine Native Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def ops : Vector BranchMode 6 := #v[.BEQ,.BNE,.BLT,.BGE,.BLTU,.BGEU]
private def oldEntry (i : Fin 6) : ProgramEntry Unit :=
  ⟨BitVec.ofNat 32 (4 * i.val),Tests.Branches.words[i],.BTYPE (8,.Regidx 2,.Regidx 1,ops[i]),
    ⟨(),1,2,0,⟨8,0⟩,16,branchFunct3 ops[i]⟩⟩
private def entry (i : Fin 6) : BranchProgramEntry :=
  ⟨BitVec.ofNat 32 (4 * i.val),Tests.Branches.words[i],.BTYPE (8,.Regidx 2,.Regidx 1,ops[i]),
    ⟨ops[i],1,2,0,⟨8,0⟩,70,branchFunct3 ops[i]⟩⟩
private def before := Tests.Branches.initial .equal .beq
private def setup : SparseDecoderSetup BranchMode := ⟨(List.finRange 6).map (some ∘ entry),2⟩

theorem all_original_fields (i : Fin 6) : branchDecoderFields (entry i).instruction = some (entry i).data := by
  fin_cases i <;> rfl

/-- Reuse only retained original public byte/stateful decoder evidence. Old
    split-family masks/native table/constraints/acceptance are not transferred. -/
theorem original_sources (i : Fin 6) : (entry i).SourceWith before branchDecoderFields := by
  have oldMember : oldEntry i ∈ Tests.Branches.setup.program := by
    fin_cases i <;> simp [oldEntry,ops,Tests.Branches.setup,Tests.Branches.words,SparseDecoderSetup.program,branchFunct3]
  have previous := (Trace.Proofs.sparse_setup_sources (Tests.Branches.program_image .equal .beq) oldMember).1
  exact ⟨previous.bytes,previous.decoded,all_original_fields i⟩

private theorem slot (i : Fin 6) :
    programSlotRunWith branchDecoderFields before (BitVec.ofNat 32 (4 * i.val)) = some (some (entry i)) := by
  have source := original_sources i
  simp only [programSlotRunWith,show (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
    .ok (entry i).bits before from source.bytes,source.decoded,bind,Option.bind,pure]
  rw [all_original_fields]
  rfl

private theorem slots (indices : List (Fin 6)) :
    (indices.map fun i => BitVec.ofNat 32 (4 * i.val)).mapM (programSlotRunWith branchDecoderFields before) =
      some (indices.map (some ∘ entry)) := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp only [List.map_cons,List.mapM_cons,slot,ih,bind,Option.bind,pure,Function.comp_apply]

theorem complete_original_image : branchDecoderSetupImage before 6 3 = some setup := by
  have image := slots (List.finRange 6)
  change ((List.range 6).map fun i => BitVec.ofNat 32 (4 * i)).mapM
    (programSlotRunWith branchDecoderFields before) = some setup.slots at image
  change (((List.range 6).map fun i => BitVec.ofNat 32 (4 * i)).mapM
    (programSlotRunWith branchDecoderFields before)).bind
      (fun entries => some (SparseDecoderSetup.mk entries 2)) = some setup
  rw [image]
  rfl

theorem original_offset_even (i : Fin 6) : (entry i).data.immediate.lo % 2 = 0 :=
  NativeBranchDecoderProofs.offset_even (original_sources i)

theorem raw_zero_operands (op : BranchMode) :
    branchDecoderFields (.BTYPE (8190,.Regidx 0,.Regidx 0,op)) =
      some ⟨op,0,0,0,⟨65534,65535⟩,70,branchFunct3 op⟩ := by
  cases op <;> rfl

theorem corrupt_funct3_rejected {w : Nat → ZMod mersenne31Modulus} (i : Fin 6)
    (query : decoderQuery w = (entry i).query) : w 11 ≠ 2 := by
  have fields := NativeBranchDecoderProofs.decoded_fields (all_original_fields i) query
  rw [fields.funct3]
  fin_cases i <;> decide +kernel

/-- Initialized native matching derives the formerly unchecked low source bound. -/
theorem initialized_source_bound {trace : Data mersenne31Modulus NativeReducedFamily}
    {publicSetup : SparseDecoderSetup BranchMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : branchDecoderSetupImage initial count logCapacity = some publicSetup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : BranchDecodedTrace (fixedData trace) publicSetup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    (sourceWord row.assignment).lo < 65536 := by
  have ranges := (public_branch_value_bounds image inputs accepted decoded).1 row present
  cases row with
  | mk family w =>
    cases family
    have first := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at first
    exact first.1

/-- Final range/alignment follows from the initialized public numerical theorem,
    with no per-row source bound, expected target or chosen-condition input. -/
theorem initialized_final_bound {trace : Data mersenne31Modulus NativeReducedFamily}
    {publicSetup : SparseDecoderSetup BranchMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : branchDecoderSetupImage initial count logCapacity = some publicSetup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : BranchDecodedTrace (fixedData trace) publicSetup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    (finalPCWord row.assignment).Bounded ∧ (finalPCWord row.assignment).toBitVec.toNat % 4 = 0 := by
  obtain ⟨_,_,_,_,_,effects⟩ := public_branch_results image inputs accepted decoded row present
  exact ⟨effects.2.2.2.2.1,effects.2.2.2.2.2.2⟩

end Tests.NativeReducedBranchDecoder
