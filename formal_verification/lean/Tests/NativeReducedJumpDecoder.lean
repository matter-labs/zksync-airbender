import Airbender.Review.Trace.Families.ReducedMachine.JumpDecoder
import Airbender.Review.Trace.Families.ReducedMachine.JumpValues
import Airbender.Review.Trace.Families.ReducedMachine.JumpResults
import Tests.JumpLink

namespace Tests.NativeReducedJumpDecoder
open Airbender Arithmetic Trace ReducedMachine Native Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def oldEntries : Vector JumpBranchSlt.ProgramEntry 3 :=
  #v[JumpBranchSlt.NativeSetup.jalEntry,Tests.JumpLink.jalrEntry,Tests.JumpLink.zeroEntry]
private def entries : Vector JumpProgramEntry 3 :=
  #v[⟨0,0xffdff0ef,.JAL (0x1ffffc,.Regidx 1),⟨true,0,0,1,⟨65532,65535⟩,33025,7⟩⟩,
     ⟨4,0x008080e7,.JALR (8,.Regidx 1,.Regidx 1),⟨false,1,0,1,⟨8,0⟩,257,0⟩⟩,
     ⟨8,0x0080006f,.JAL (8,.Regidx 0),⟨true,0,0,0,⟨8,0⟩,33025,0⟩⟩]
private def setup : SparseDecoderSetup JumpMode := ⟨(List.finRange 3).map (fun i => some entries[i]),1⟩

theorem original_fields (i : Fin 3) : jumpDecoderFields entries[i].instruction = some entries[i].data := by
  fin_cases i <;> rfl

/-- Reuse ONLY original byte/stateful Sail decoder evidence, never old split
    native masks/tables/constraints/accepted traces. -/
theorem original_sources (i : Fin 3) : entries[i].SourceWith Tests.JumpLink.before jumpDecoderFields := by
  have member : oldEntries[i] ∈ Tests.JumpLink.setup.program := by
    fin_cases i <;> simp [oldEntries,Tests.JumpLink.setup,SparseDecoderSetup.program]
  have previous := (Trace.Proofs.sparse_setup_sources Tests.JumpLink.program_image member).1
  have pc : entries[i].pc = oldEntries[i].pc := by fin_cases i <;> rfl
  have bits : entries[i].bits = oldEntries[i].bits := by fin_cases i <;> rfl
  have instruction : entries[i].instruction = oldEntries[i].instruction := by fin_cases i <;> rfl
  exact ⟨by simpa only [pc,bits] using previous.bytes,
    by simpa only [bits,instruction] using previous.decoded,original_fields i⟩

private theorem slot (i : Fin 3) :
    programSlotRunWith jumpDecoderFields Tests.JumpLink.before (BitVec.ofNat 32 (4 * i.val)) = some (some entries[i]) := by
  have pc : entries[i].pc = BitVec.ofNat 32 (4 * i.val) := by fin_cases i <;> rfl
  have source := original_sources i
  simp only [programSlotRunWith,show (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read Tests.JumpLink.before =
    .ok entries[i].bits Tests.JumpLink.before from pc ▸ source.bytes,source.decoded,bind,Option.bind,pure]
  rw [original_fields]
  fin_cases i <;> rfl

private theorem slots (indices : List (Fin 3)) :
    (indices.map fun i => BitVec.ofNat 32 (4 * i.val)).mapM
      (programSlotRunWith jumpDecoderFields Tests.JumpLink.before) = some (indices.map fun i => some entries[i]) := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp only [List.map_cons,List.mapM_cons,slot,ih,bind,Option.bind,pure]

theorem complete_original_image : jumpDecoderSetupImage Tests.JumpLink.before 3 2 = some setup := by
  have image := slots (List.finRange 3)
  change ((List.range 3).map fun i => BitVec.ofNat 32 (4 * i)).mapM
    (programSlotRunWith jumpDecoderFields Tests.JumpLink.before) = some setup.slots at image
  change (((List.range 3).map fun i => BitVec.ofNat 32 (4 * i)).mapM
    (programSlotRunWith jumpDecoderFields Tests.JumpLink.before)).bind
      (fun entries => some (SparseDecoderSetup.mk entries 1)) = some setup
  rw [image]
  rfl

theorem negative_zero_operands :
    jumpDecoderFields (.JAL (0x1ffffc,.Regidx 0)) =
      some ⟨true,0,0,0,⟨65532,65535⟩,33025,7⟩ ∧
    jumpDecoderFields (.JALR (4095,.Regidx 1,.Regidx 0)) =
      some ⟨false,1,0,0,⟨65535,65535⟩,257,0⟩ := ⟨rfl,rfl⟩

theorem original_direct_parity (i : Fin 3) (direct : entries[i].data.family = true) :
    entries[i].data.immediate.lo % 2 = 0 := NativeJumpDecoderProofs.offset_even (original_sources i) direct

theorem corrupt_raw_tag_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = entries[0].query) : w 11 ≠ 0 := by
  rw [(NativeJumpDecoderProofs.decoded_fields (original_fields 0) query).funct3]
  decide +kernel

theorem corrupt_zero_flag_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = entries[2].query) : rdZeroFlag w ≠ 0 := by
  rw [(NativeJumpDecoderProofs.decoded_fields (original_fields 2) query).zero]
  decide +kernel

/-- Actual canonical link return wraps even when the outgoing jump target is
    different; this is a conditional native consequence, not a full row witness. -/
theorem native_return_wrap {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table))
    (query : decoderQuery w = (⟨0xfffffffc,0x008001ef,.JAL (8,.Regidx 3),
      ⟨true,0,0,3,⟨8,0⟩,33025,0⟩⟩ : JumpProgramEntry).query) : candidateWord w = ⟨0,0⟩ := by
  have fields : jumpDecoderFields (.JAL (8,.Regidx 3)) =
      some (⟨true,0,0,3,⟨8,0⟩,33025,0⟩ : DecoderData JumpMode) := rfl
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec (0xfffffffc : BitVec 32) at canonical
  have aligned : (initialPCWord w).lo % 4 = 0 := by rw [canonical]; decide +kernel
  have result := (NativeJumpReturnProofs.candidate_result native fields query aligned).1
  rw [result,canonical]
  decide +kernel

theorem independent_reference_targets :
    JumpMode.target true 0 0 0xfffffffc = 0xfffffffc ∧
    JumpMode.target true 0xfffffffc 0 8 = 4 ∧
    JumpMode.target false 4 257 8 = 264 ∧
    JumpMode.target false 0 3 0xfffffffe = 0 := by decide +kernel

/-- Initialized matching derives the formerly unchecked low source bound. -/
theorem initialized_source_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {publicSetup : SparseDecoderSetup JumpMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : jumpDecoderSetupImage initial count logCapacity = some publicSetup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : JumpDecodedTrace (fixedData trace) publicSetup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    (sourceWord row.assignment).lo < 65536 := by
  have ranges := (public_jump_value_bounds image inputs accepted decoded).1 row present
  cases row with
  | mk family w =>
    cases family
    have first := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at first
    exact first.1

end Tests.NativeReducedJumpDecoder
