import Airbender.Review.Circuits.ReducedMachine.JumpResult
import Airbender.Proofs.ReducedMachine.NativeJumpDecoder
import Airbender.Proofs.ReducedMachine.NativeJumpFields
import Airbender.Proofs.ReducedMachine.NativePC

namespace Airbender.ReducedMachine.NativeJumpReturnProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original query supplies incoming canonical bounds; the actual increment
    derives default return bounds/full RV32 wrap before any range induction. -/
theorem link_successor {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : JumpProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (query : decoderQuery w = entry.query) (aligned : (initialPCWord w).lo % 4 = 0) :
    (jumpLinkWord w).Bounded ∧ (jumpLinkWord w).toBitVec = (initialPCWord w).toBitVec+4 := by
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  have pc : (initialPCWord w).Bounded := by rw [canonical]; exact Word.ofBitVec_bound _
  exact NativePCProofs.default_pc_successor (by decide : 196608 < mersenne31Modulus) native
    (initial := initialPCWord w) (final := jumpLinkWord w)
    ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,rfl,rfl⟩ pc aligned

/-- Exact native return candidate and original-rd/x0 masked write. Alignment is
    internal, derived from public instruction membership before initialized use. -/
theorem candidate_result {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : JumpProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : jumpDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (aligned : (initialPCWord w).lo % 4 = 0) :
    candidateWord w = Word.ofBitVec ((initialPCWord w).toBitVec+4) ∧
    writtenWord w = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec ((initialPCWord w).toBitVec+4) := by
  have decoded := NativeJumpDecoderProofs.decoded_fields fields query
  have link := link_successor native query aligned
  have actual := NativeJumpFieldProofs.candidate native entry.data.family decoded.mask
  have lo := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
  have hi := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
  have same : candidateWord w = jumpLinkWord w := by
    simp [jumpCandidate,defaultPC] at lo hi
    simp [candidateWord,jumpLinkWord,lo,hi]
  have result : candidateWord w = Word.ofBitVec ((initialPCWord w).toBitVec+4) := by
    rw [same]
    apply Word.eq_of_value link.1 (Word.ofBitVec_bound _)
    rw [Word.ofBitVec_value,← link.2,Word.toBitVec_toNat link.1]
  refine ⟨result,?_⟩
  have write := (NativeJumpFieldProofs.write native entry.data.family decoded.mask).2
  have first := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) write
  have second := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) write
  by_cases zero : entry.data.rd = 0
  · rw [if_pos zero]
    have flag : rdZeroFlag w = 1 := by rw [decoded.zero,if_pos zero]
    simp [flag,jumpCandidate] at first second
    simp [writtenWord,first,second]
  · rw [if_neg zero]
    have flag : rdZeroFlag w = 0 := by rw [decoded.zero,if_neg zero]
    simp [flag,jumpCandidate] at first second
    simpa only [writtenWord,first,second,candidateWord] using result

end Airbender.ReducedMachine.NativeJumpReturnProofs
