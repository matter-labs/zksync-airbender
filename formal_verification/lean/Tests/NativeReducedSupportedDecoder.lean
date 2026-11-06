import Airbender.Review.Trace.Families.ReducedMachine.SupportedDecoder
import Airbender.Proofs.ShiftBinop.NativeSetup

namespace Tests.NativeReducedSupportedDecoder
open Airbender Arithmetic Trace ReducedMachine Native
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Reuse only exact original public bytes/state and Sail decoder lemmas. No old
-- split-family mask, native table or constraint identity is transferred.
private def slot (i : Fin 25) : Option SupportedProgramEntry :=
  (supportedDecoderFields ShiftBinop.NativeSetup.instructions[i.val]).map fun data =>
    ⟨BitVec.ofNat 32 (4 * i.val),ShiftBinop.NativeSetup.words[i.val],
      ShiftBinop.NativeSetup.instructions[i.val],data⟩
private def setup : SparseDecoderSetup SupportedMode := ⟨(List.finRange 25).map slot,7⟩

/-- Original byte reads/stateful decoding construct all slots with the new
    actual reduced projection, including both selected shifts and ADD. -/
theorem original_public_slots (i : Fin 25) :
    programSlotRunWith supportedDecoderFields ShiftBinop.NativeSetup.before (BitVec.ofNat 32 (4 * i.val)) =
      some (slot i) := by
  simp only [programSlotRunWith,ShiftBinop.Proofs.native_fixture_words,
    ShiftBinop.Proofs.native_fixture_decode,bind,Option.bind,pure,slot]

private theorem map_slots (indices : List (Fin 25)) :
    (indices.map fun i => BitVec.ofNat 32 (4 * i.val)).mapM
      (programSlotRunWith supportedDecoderFields ShiftBinop.NativeSetup.before) = some (indices.map slot) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.map_cons,List.mapM_cons,original_public_slots,ih,bind,Option.bind,pure]

/-- Complete public prefix/tail construction now accepts the original ADD at
    PC96 and original bitwise forms at their original PCs in the same image. -/
theorem mixed_public_image : supportedDecoderSetupImage ShiftBinop.NativeSetup.before 25 5 = some setup := by
  have image := map_slots (List.finRange 25)
  change ((List.range 25).map fun i => BitVec.ofNat 32 (4 * i)).mapM
    (programSlotRunWith supportedDecoderFields ShiftBinop.NativeSetup.before) = some setup.slots at image
  change (((List.range 25).map fun i => BitVec.ofNat 32 (4 * i)).mapM
    (programSlotRunWith supportedDecoderFields ShiftBinop.NativeSetup.before)).bind
      (fun entries => some (SparseDecoderSetup.mk entries 7)) = some setup
  rw [image]
  rfl

private def first : SupportedProgramEntry :=
  ⟨0,0x002091b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLL),⟨.inl .left,1,2,3,⟨0,0⟩,4099,1⟩⟩
private def last : SupportedProgramEntry :=
  ⟨96,0x001080b3,.RTYPE (.Regidx 1,.Regidx 1,.Regidx 1,.ADD),⟨.inr (.inl .add),1,1,1,⟨0,0⟩,11,0⟩⟩

/-- Both profiles have original bytes and stateful Sail source evidence in one
    complete public image, rather than an assumed per-row classification. -/
theorem original_mixed_sources :
    first.SourceWith ShiftBinop.NativeSetup.before supportedDecoderFields ∧
      last.SourceWith ShiftBinop.NativeSetup.before supportedDecoderFields := by
  have firstSlot : some first ∈ setup.slots := List.getElem_mem (l := setup.slots) (n := 0) (by decide)
  have lastSlot : some last ∈ setup.slots := List.getElem_mem (l := setup.slots) (n := 24) (by decide)
  have firstMember : first ∈ setup.program := List.mem_filterMap.mpr ⟨some first,firstSlot,rfl⟩
  have lastMember : last ∈ setup.program := List.mem_filterMap.mpr ⟨some last,lastSlot,rfl⟩
  exact ⟨(Trace.Proofs.run_sparse_setup_sources mixed_public_image firstMember).1,
    (Trace.Proofs.run_sparse_setup_sources mixed_public_image lastMember).1⟩

/-- New projection retains actual native masks, x0 constructors, encoded SRAI
    and raw U-type funct3, without using old split-family decoder masks. -/
theorem selected_fields :
    supportedDecoderFields first.instruction = some first.data ∧
    supportedDecoderFields last.instruction = some last.data ∧
    supportedDecoderFields (.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SRAI)) =
      some ⟨.inl .arithmetic,1,0,0,⟨1055,0⟩,102401,5⟩ ∧
    supportedDecoderFields (.ITYPE (4095,.Regidx 1,.Regidx 0,.ADDI)) =
      some ⟨.inr (.inl .addi),1,0,0,⟨65535,65535⟩,9,0⟩ ∧
    supportedDecoderFields (.UTYPE (7,.Regidx 0,.LUI)) =
      some ⟨.inr (.inl .lui),0,0,0,⟨28672,0⟩,513,7⟩ ∧
    supportedDecoderFields (.UTYPE (5,.Regidx 4,.AUIPC)) =
      some ⟨.inr (.inl .auipc),0,0,4,⟨20480,0⟩,17,5⟩ := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Original bitwise support fills the old hole; oversized shifts remain
    unsupported. This checks the exact intended profile extension. -/
theorem unsupported_holes :
    (setup.slots[3]?).bind id ≠ none ∧
    supportedDecoderFields (.SHIFTIOP (32,.Regidx 1,.Regidx 3,.SLLI)) = none ∧
    supportedDecoderFields (.SHIFTIOP (63,.Regidx 1,.Regidx 0,.SRAI)) = none := by
  exact ⟨by decide,rfl,rfl⟩

/-- Complete setup contains both actual queries and its padding. Native Boolean
    packing, not an added exclusion premise, prevents selecting that sentinel. -/
theorem queries_and_padding {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table)) :
    (setup.table (p := mersenne31Modulus)).Contains #[] first.query ∧ (setup.table (p := mersenne31Modulus)).Contains #[] last.query ∧
      (setup.table (p := mersenne31Modulus)).Contains #[] (Vector.replicate 10 (-1)) ∧ decoderQuery w ≠ Vector.replicate 10 (-1) := by
  exact ⟨⟨⟨0,by decide⟩,rfl⟩,⟨⟨24,by decide⟩,rfl⟩,
    ⟨⟨31,by decide⟩,rfl⟩,NativeShiftDecoderProofs.padding_excluded native⟩

/-- The original U-type raw funct3 remains observable in the common query. -/
theorem corrupted_upper_funct3_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = (⟨8,0x00005217,.UTYPE (5,.Regidx 4,.AUIPC),
      ⟨.inr (.inl .auipc),0,0,4,⟨20480,0⟩,17,5⟩⟩ : SupportedProgramEntry).query) : w 11 ≠ 0 := by
  have selected := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[8]) query
  change w 11 = 5 at selected
  rw [selected]
  decide +kernel


/-- All original bitwise slots, including x0 and both immediate signs, coexist
    with shift/ADD in the complete public image. Every slot is now supported. -/
theorem complete_original_image (i : Fin 25) : ∃ entry, setup.slots[i.val]? = some (some entry) ∧
    entry.SourceWith ShiftBinop.NativeSetup.before supportedDecoderFields := by
  have supported : ∃ entry, setup.slots[i.val]? = some (some entry) := by
    fin_cases i <;> exact ⟨_,rfl⟩
  obtain ⟨entry,found⟩ := supported
  have member : some entry ∈ setup.slots := List.mem_of_getElem? found
  have present : entry ∈ setup.program := List.mem_filterMap.mpr ⟨some entry,member,rfl⟩
  exact ⟨entry,found,(Trace.Proofs.run_sparse_setup_sources mixed_public_image present).1⟩

end Tests.NativeReducedSupportedDecoder
