import Airbender.Review.Trace.Families.ReducedMachine.CSRDecoder

namespace Tests.NativeReducedCSRDecoder
open Airbender Arithmetic Trace ReducedMachine Native
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Independent original bytes, not the retained native eight-word ROM image.
private def before : State :=
  { (default : State) with
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 0xf3 |>.insert 1 0x91 |>.insert 2 0 |>.insert 3 0x7c
      |>.insert 4 0x73 |>.insert 5 0x10 |>.insert 6 0x71 |>.insert 7 0x7c
      |>.insert 8 0xf3 |>.insert 9 0xa1 |>.insert 10 0 |>.insert 11 0x7c) }
private def words : Vector (BitVec 32) 3 := #v[0x7c0091f3,0x7c711073,0x7c00a1f3]
private def instructions : Vector SailRV32.instruction 3 :=
  #v[.CSRReg (1984,.Regidx 1,.Regidx 3,.CSRRW),
    .CSRReg (1991,.Regidx 2,.Regidx 0,.CSRRW),
    .CSRReg (1984,.Regidx 1,.Regidx 3,.CSRRS)]
private def slots : List (Option CSRProgramEntry) :=
  (List.finRange 3).map fun i => (csrDecoderFields instructions[i]).map fun data =>
    ⟨BitVec.ofNat 32 (4 * i.val),words[i],instructions[i],data⟩
private def setup : SparseDecoderSetup CSRMode := ⟨slots,1⟩

private theorem public_words (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before = .ok words[i] before := by
  fin_cases i <;> simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
    before,words,Std.ExtHashMap.getElem_insert]

private theorem csr_enabled : SailRV32.Functions.currentlyEnabled .Ext_Zicsr = .pure true := by
  rw [SailRV32.Functions.currentlyEnabled,SailRV32.Functions.hartSupports]
  rfl

private theorem original_decoders (i : Fin 3) :
    SailRV32.Functions.encdec_backwards words[i] = .pure instructions[i] := by
  fin_cases i <;> dsimp only [words,instructions]
  all_goals dsimp only [SailRV32.Functions.encdec_backwards]
  all_goals rw [csr_enabled]
  all_goals rfl

private theorem public_slot (i : Fin 3) :
    programSlotRunWith csrDecoderFields before (BitVec.ofNat 32 (4 * i.val)) =
      some ((csrDecoderFields instructions[i]).map fun data =>
        (⟨BitVec.ofNat 32 (4 * i.val),words[i],instructions[i],data⟩ : CSRProgramEntry)) := by
  simp only [programSlotRunWith,public_words,original_decoders,bind,Option.bind,pure]
  rfl

/-- Complete original public sparse image, including an unsupported CSRRS hole and
    the separate padding row. This is not native ROM/export/physical fidelity. -/
theorem complete_original_image : csrDecoderSetupImage before 3 2 = some setup := by
  have fetched : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotRunWith csrDecoderFields before) = some slots := by
    simp only [List.mapM_cons,List.mapM_nil,
      show programSlotRunWith csrDecoderFields before 0 = _ from public_slot 0,
      show programSlotRunWith csrDecoderFields before 4 = _ from public_slot 1,
      show programSlotRunWith csrDecoderFields before 8 = _ from public_slot 2,
      bind,Option.bind,pure]
    rfl
  change (([0,4,8] : List (BitVec 32)).mapM
    (programSlotRunWith csrDecoderFields before)).bind
      (fun entries => some (SparseDecoderSetup.mk entries 1)) = some setup
  rw [fetched]
  rfl

/-- Both original CSRRW entries have real public byte and
    stateful decoder evidence; no old standalone native acceptance is reused. -/
theorem original_sources (i : Fin 2) :
    ∃ entry, setup.slots[i.val]? = some (some entry) ∧
      entry.SourceWith before csrDecoderFields := by
  have filled : ∃ entry, setup.slots[i.val]? = some (some entry) := by
    fin_cases i <;> exact ⟨_,rfl⟩
  obtain ⟨entry,found⟩ := filled
  have member : entry ∈ setup.program := List.mem_filterMap.mpr
    ⟨some entry,List.mem_of_getElem? found,rfl⟩
  exact ⟨entry,found,(Trace.Proofs.run_sparse_setup_sources complete_original_image member).1⟩

/-- Every raw original CSR index/operand pair retains its exact unsigned fields,
    including both nonzero rs1/rd; no standalone operand restriction is imported. -/
theorem raw_fields (index : BitVec 12) (rs1 rd : BitVec 5) :
    csrDecoderFields (.CSRReg (index,.Regidx rs1,.Regidx rd,.CSRRW)) =
      some ⟨(),rs1,0,rd,⟨index.toNat,0⟩,129,1⟩ := rfl

theorem unsigned_high_index :
    csrDecoderFields (.CSRReg (4095,.Regidx 0,.Regidx 0,.CSRRW)) =
      some ⟨(),0,0,0,⟨4095,0⟩,129,1⟩ := rfl

/-- CSRRS/CSRRC/immediate CSR and unrelated instructions remain holes. -/
theorem unsupported_forms :
    csrDecoderFields (.CSRReg (1984,.Regidx 1,.Regidx 3,.CSRRS)) = none ∧
    csrDecoderFields (.CSRReg (1984,.Regidx 1,.Regidx 3,.CSRRC)) = none ∧
    csrDecoderFields (.CSRImm (1984,1,.Regidx 3,.CSRRW)) = none ∧
    csrDecoderFields (.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.ADD)) = none :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem complete_hole_and_tail : setup.slots[2]? = some none ∧
    setup.table.Contains #[] (Vector.replicate 10 (-1 : ZMod mersenne31Modulus)) :=
  ⟨rfl,⟨⟨2,by decide⟩,rfl⟩⟩

theorem native_sentinel_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed)) :
    decoderQuery w ≠ Vector.replicate 10 (-1) := NativeShiftDecoderProofs.padding_excluded holds

private def zeroCSR : CSRProgramEntry :=
  ⟨0,0xfff01073,.CSRReg (4095,.Regidx 0,.Regidx 0,.CSRRW),
    ⟨(),0,0,0,⟨4095,0⟩,129,1⟩⟩
private theorem zero_fields : csrDecoderFields zeroCSR.instruction = some zeroCSR.data := rfl

theorem corrupt_tag_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = zeroCSR.query) : w 11 ≠ 0 := by
  rw [(NativeCSRDecoderProofs.decoded_fields zero_fields query).funct3]
  decide +kernel

theorem corrupt_zero_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = zeroCSR.query) : rdZeroFlag w ≠ 0 := by
  rw [(NativeCSRDecoderProofs.decoded_fields zero_fields query).zero]
  decide +kernel

theorem nonzero_rs2_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = zeroCSR.query) : w 6 ≠ 1 := by
  rw [(NativeCSRDecoderProofs.decoded_fields zero_fields query).rs2]
  decide +kernel

/-- The top CSR bit never sign-extends into the upper native immediate limb. -/
theorem canonical_unsigned_key {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = zeroCSR.query) : (w 9).val < 4096 ∧ w 10 = 0 :=
  NativeCSRDecoderProofs.key_bounds zero_fields query

/-- Full public construction succeeds with empty registers: original CSR decoding
    adds no CSR-availability or privileged-execution premise. -/
theorem no_decode_CSR_availability : before.regs = (default : State).regs ∧
    csrDecoderSetupImage before 3 2 = some setup := ⟨rfl,complete_original_image⟩

section ConditionalTrace
variable {trace : Data mersenne31Modulus NativeReducedFamily}
    {publicSetup : SparseDecoderSetup CSRMode} {initial : State} {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some publicSetup)
    (accepted : Accepted (runtimeCSRData trace)) (decoded : CSRDecodedTrace trace publicSetup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows)
include image accepted decoded present

/-- No explicit local mask or per-row profile is supplied to this root. -/
theorem original_source_runtime_domain :
    ∃ entry ∈ publicSetup.program, entry.SourceWith initial csrDecoderFields ∧
      row.decoderQuery = entry.query ∧ CSRDecoded row.assignment entry ∧
      ((row.assignment 9).val = 1984 ∨ (row.assignment 9).val = 1991) := by
  obtain ⟨entry,found,source,query,fields,effects⟩ :=
    public_runtime_csr_effects image accepted decoded row present
  exact ⟨entry,found,source,query,fields,effects.key⟩

theorem bigint_public_row_rejected (key : (row.assignment 9).val = 1994) : False := by
  obtain ⟨entry,found,source,query,fields,effects⟩ :=
    public_runtime_csr_effects image accepted decoded row present
  have domain := effects.key
  omega
end ConditionalTrace
end Tests.NativeReducedCSRDecoder
