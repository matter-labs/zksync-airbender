import Airbender.Review.Trace.Families.ReducedMachine.UnifiedDecoder

namespace Tests.NativeReducedUnifiedDecoder
open Airbender Arithmetic Trace ReducedMachine Native
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Independent original byte image, unrelated to the native fixed eight-word ROM.
private def before : State :=
  { (default : State) with
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 0x83 |>.insert 1 0xa1 |>.insert 2 0 |>.insert 3 1
      |>.insert 4 0x23 |>.insert 5 0xa8 |>.insert 6 0x20 |>.insert 7 0
      |>.insert 8 0xb3 |>.insert 9 0x81 |>.insert 10 0x20 |>.insert 11 0) }
private def words : Vector (BitVec 32) 3 := #v[0x0100a183,0x0020a823,0x002081b3]
private def instructions : Vector SailRV32.instruction 3 :=
  #v[.LOAD (16,.Regidx 1,.Regidx 3,false,4),.STORE (16,.Regidx 2,.Regidx 1,4),
    .RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.ADD)]
private def slots : List (Option UnifiedProgramEntry) :=
  (List.finRange 3).map fun i => (unifiedDecoderFields instructions[i]).map fun data =>
    ⟨BitVec.ofNat 32 (4 * i.val),words[i],instructions[i],data⟩
private def setup : SparseDecoderSetup UnifiedMode := ⟨slots,1⟩

private theorem public_words (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before = .ok words[i] before := by
  fin_cases i <;> simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
    before,words,Std.ExtHashMap.getElem_insert]

private theorem public_slot (i : Fin 3) :
    programSlotRunWith unifiedDecoderFields before (BitVec.ofNat 32 (4 * i.val)) =
      some ((unifiedDecoderFields instructions[i]).map fun data =>
        (⟨BitVec.ofNat 32 (4 * i.val),words[i],instructions[i],data⟩ : UnifiedProgramEntry)) := by
  simp only [programSlotRunWith,public_words,bind,Option.bind]
  fin_cases i <;> rfl

/-- Complete original public sparse image, including retained ADD beside LW/SW and
    the separate padding row. This is not native ROM/export/physical fidelity. -/
theorem complete_original_image : unifiedDecoderSetupImage before 3 2 = some setup := by
  have fetched : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotRunWith unifiedDecoderFields before) = some slots := by
    simp only [List.mapM_cons,List.mapM_nil,
      show programSlotRunWith unifiedDecoderFields before 0 = _ from public_slot 0,
      show programSlotRunWith unifiedDecoderFields before 4 = _ from public_slot 1,
      show programSlotRunWith unifiedDecoderFields before 8 = _ from public_slot 2,
      bind,Option.bind,pure]
    rfl
  change (([0,4,8] : List (BitVec 32)).mapM
    (programSlotRunWith unifiedDecoderFields before)).bind
      (fun entries => some (SparseDecoderSetup.mk entries 1)) = some setup
  rw [fetched]
  rfl

/-- All three retained original constructors have real public byte and
    stateful decoder evidence; no old standalone native acceptance is reused. -/
theorem original_sources (i : Fin 3) :
    ∃ entry, setup.slots[i.val]? = some (some entry) ∧
      entry.SourceWith before unifiedDecoderFields := by
  have filled : ∃ entry, setup.slots[i.val]? = some (some entry) := by
    fin_cases i <;> exact ⟨_,rfl⟩
  obtain ⟨entry,found⟩ := filled
  have member : entry ∈ setup.program := List.mem_filterMap.mpr
    ⟨some entry,List.mem_of_getElem? found,rfl⟩
  exact ⟨entry,found,(Trace.Proofs.run_sparse_setup_sources complete_original_image member).1⟩

/-- Independent encoded fields cover all seven profiles (both memory modes).
    This projection check alone is not native row acceptance or execution. -/
theorem seven_profile_masks :
    ([.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLL),
      .RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.ADD),
      .RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.XOR),
      .RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLTU),
      .BTYPE (4,.Regidx 2,.Regidx 1,.BEQ),.JAL (4,.Regidx 3),
      .LOAD (16,.Regidx 1,.Regidx 3,false,4),.STORE (16,.Regidx 2,.Regidx 1,4)] :
        List SailRV32.instruction).map (fun instruction => (unifiedDecoderFields instruction).map (·.mask)) =
      [some 4099,some 11,some 35,some 67,some 70,some 33025,some 1025,some 16386] := rfl

theorem negative_zero_fields :
    unifiedDecoderFields (.LOAD (4095,.Regidx 0,.Regidx 0,false,4)) =
      some ⟨.inr false,0,0,0,⟨65535,65535⟩,1025,2⟩ ∧
    unifiedDecoderFields (.STORE (4095,.Regidx 0,.Regidx 0,4)) =
      some ⟨.inr true,0,0,0,⟨65535,65535⟩,16386,2⟩ := ⟨rfl,rfl⟩

/-- The formerly unsupported ADD slot is now filled; separate padding remains. -/
theorem complete_program_and_tail : setup.program.length = 3 ∧
    (∃ entry, setup.slots[2]? = some (some entry) ∧
      setup.table.Contains #[] (entry.query (p := mersenne31Modulus))) ∧
    setup.table.Contains #[] (Vector.replicate 10 (-1 : ZMod mersenne31Modulus)) := by
  refine ⟨rfl,⟨_,rfl,⟨⟨2,by decide⟩,rfl⟩⟩,⟨⟨3,by decide⟩,rfl⟩⟩

theorem unsupported_subwords_and_native_padding {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed)) :
    unifiedDecoderFields (.LOAD (0,.Regidx 1,.Regidx 3,false,1)) = none ∧
    unifiedDecoderFields (.STORE (0,.Regidx 2,.Regidx 1,2)) = none ∧
    decoderQuery w ≠ Vector.replicate 10 (-1) :=
  ⟨rfl,rfl,NativeShiftDecoderProofs.padding_excluded holds⟩

end Tests.NativeReducedUnifiedDecoder
