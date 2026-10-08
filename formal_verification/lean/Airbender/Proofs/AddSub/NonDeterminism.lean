import Airbender.Review.AddSub.NonDeterminism
import Airbender.Proofs.AddSub.PC
import Airbender.Proofs.Sail.PC
import Airbender.Proofs.AddSub

namespace Airbender.AddSub.Proofs
open Arithmetic Reference.RiscV Reference.Sail

theorem nondeterminism_write_soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (NonDeterminism.writeModel (p := p)).SoundnessUnder
      NonDeterminism.WriteInterfaces NonDeterminism.writeSpec := by
  rintro input finalPC w ⟨interfaces, constraints, mapping, _⟩
  obtain ⟨_, _, pc⟩ := pc_successor hp inverse constraints mapping interfaces.initialPCBounds
  exact Reference.RiscV.Sail.retire_no_write interfaces.pcRead pc

/-- Reuse the same imported output ranges, PC proof and native retirement rule.
    Stream agreement comes only from the explicitly named external port mapping. -/
theorem nondeterminism_read_soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (NonDeterminism.readModel (p := p)).SoundnessUnder
      NonDeterminism.ReadInterfaces NonDeterminism.readSpec := by
  rintro input output w ⟨interfaces, constraints, mapping⟩
  obtain ⟨response, responseRead, lo, hi⟩ := mapping.responsePort
  have responseBounds := Word.ofBitVec_bound response
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have equal : output.destination = Word.ofBitVec response := by
    have lowEq := mapping.outputLo
    have highEq := mapping.outputHi
    rw [lo, ZMod.val_natCast_of_lt (lt_trans responseBounds.1 limbSize)] at lowEq
    rw [hi, ZMod.val_natCast_of_lt (lt_trans responseBounds.2 limbSize)] at highEq
    exact congrArg₂ Word.mk lowEq highEq
  obtain ⟨_, _, pc⟩ := pc_successor hp inverse constraints mapping.pc interfaces.initialPCBounds
  have bounds := written_limb_bounds constraints
  refine ⟨response, responseRead, ⟨mapping.outputLo ▸ bounds.1, mapping.outputHi ▸ bounds.2⟩, ?_⟩
  apply Sail.retire_of_destination interfaces.pcRead pc
  obtain ⟨after, write⟩ := Sail.write_success input.rd output.destination.toBitVec
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have value : output.destination.toBitVec = response := by
    rw [equal, Word.ofBitVec_roundtrip]
  have effect := run_bind_of_ok _
    (fun (_ : Unit) => (pure SailRV32.Functions.RETIRE_SUCCESS : SailRV32.SailM _)) _ _ _ write
  refine ⟨after, ?_, ?_⟩
  · rw [← value]
    exact effect
  · exact effect

end Airbender.AddSub.Proofs
