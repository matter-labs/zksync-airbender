import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryDecoder

namespace Tests.NativeReducedWordMemoryDecoder
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
private def slots : List (Option WordMemoryProgramEntry) :=
  (List.finRange 3).map fun i => (wordMemoryDecoderFields instructions[i]).map fun data =>
    ⟨BitVec.ofNat 32 (4 * i.val),words[i],instructions[i],data⟩
private def setup : SparseDecoderSetup WordMemoryMode := ⟨slots,1⟩

private theorem public_words (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before = .ok words[i] before := by
  fin_cases i <;> simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
    before,words,Std.ExtHashMap.getElem_insert]

private theorem public_slot (i : Fin 3) :
    programSlotRunWith wordMemoryDecoderFields before (BitVec.ofNat 32 (4 * i.val)) =
      some ((wordMemoryDecoderFields instructions[i]).map fun data =>
        (⟨BitVec.ofNat 32 (4 * i.val),words[i],instructions[i],data⟩ : WordMemoryProgramEntry)) := by
  simp only [programSlotRunWith,public_words,bind,Option.bind]
  fin_cases i <;> rfl

/-- Complete original public sparse image, including an unsupported ADD hole and
    the separate padding row. This is not native ROM/export/physical fidelity. -/
theorem complete_original_image : wordMemoryDecoderSetupImage before 3 2 = some setup := by
  have fetched : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotRunWith wordMemoryDecoderFields before) = some slots := by
    simp only [List.mapM_cons,List.mapM_nil,
      show programSlotRunWith wordMemoryDecoderFields before 0 = _ from public_slot 0,
      show programSlotRunWith wordMemoryDecoderFields before 4 = _ from public_slot 1,
      show programSlotRunWith wordMemoryDecoderFields before 8 = _ from public_slot 2,
      bind,Option.bind,pure]
    rfl
  change (([0,4,8] : List (BitVec 32)).mapM
    (programSlotRunWith wordMemoryDecoderFields before)).bind
      (fun entries => some (SparseDecoderSetup.mk entries 1)) = some setup
  rw [fetched]
  rfl

/-- Both retained original word-memory constructors have real public byte and
    stateful decoder evidence; no old standalone native acceptance is reused. -/
theorem original_sources (i : Fin 2) :
    ∃ entry, setup.slots[i.val]? = some (some entry) ∧
      entry.SourceWith before wordMemoryDecoderFields := by
  have filled : ∃ entry, setup.slots[i.val]? = some (some entry) := by
    fin_cases i <;> exact ⟨_,rfl⟩
  obtain ⟨entry,found⟩ := filled
  have member : entry ∈ setup.program := List.mem_filterMap.mpr
    ⟨some entry,List.mem_of_getElem? found,rfl⟩
  exact ⟨entry,found,(Trace.Proofs.run_sparse_setup_sources complete_original_image member).1⟩

theorem negative_zero_fields :
    wordMemoryDecoderFields (.LOAD (4095,.Regidx 0,.Regidx 0,false,4)) =
      some ⟨false,0,0,0,⟨65535,65535⟩,1025,2⟩ ∧
    wordMemoryDecoderFields (.STORE (4095,.Regidx 0,.Regidx 0,4)) =
      some ⟨true,0,0,0,⟨65535,65535⟩,16386,2⟩ := ⟨rfl,rfl⟩

theorem unsupported_forms :
    wordMemoryDecoderFields (.LOAD (0,.Regidx 1,.Regidx 3,false,1)) = none ∧
    wordMemoryDecoderFields (.LOAD (0,.Regidx 1,.Regidx 3,true,2)) = none ∧
    wordMemoryDecoderFields (.STORE (0,.Regidx 2,.Regidx 1,2)) = none ∧
    wordMemoryDecoderFields instructions[2] = none := ⟨rfl,rfl,rfl,rfl⟩

theorem complete_hole_and_tail : setup.slots[2]? = some none ∧
    setup.table.Contains #[] (Vector.replicate 10 (-1 : ZMod mersenne31Modulus)) :=
  ⟨rfl,⟨⟨2,by decide⟩,rfl⟩⟩

theorem native_sentinel_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed)) :
    decoderQuery w ≠ Vector.replicate 10 (-1) := NativeShiftDecoderProofs.padding_excluded holds

private def zeroLoad : WordMemoryProgramEntry :=
  ⟨0,0xfff02003,.LOAD (4095,.Regidx 0,.Regidx 0,false,4),
    ⟨false,0,0,0,⟨65535,65535⟩,1025,2⟩⟩
private theorem zero_fields : wordMemoryDecoderFields zeroLoad.instruction = some zeroLoad.data := rfl

theorem corrupt_tag_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = zeroLoad.query) : w 11 ≠ 0 := by
  rw [(NativeWordMemoryDecoderProofs.decoded_fields zero_fields query).funct3]
  decide +kernel

theorem corrupt_zero_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = zeroLoad.query) : rdZeroFlag w ≠ 0 := by
  rw [(NativeWordMemoryDecoderProofs.decoded_fields zero_fields query).zero]
  decide +kernel

theorem canonical_negative_immediate {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = zeroLoad.query) : wordMemoryImmediateWord w = ⟨65535,65535⟩ :=
  NativeWordMemoryDecoderProofs.immediate_word zero_fields query

end Tests.NativeReducedWordMemoryDecoder
