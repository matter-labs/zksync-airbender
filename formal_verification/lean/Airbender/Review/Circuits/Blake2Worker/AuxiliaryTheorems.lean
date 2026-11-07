import Airbender.Proofs.Blake2Worker.NativeAuxiliary

namespace Airbender.Blake2Worker.Native
open AuxiliaryArtifact

theorem auxiliary_row_balance {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {w : Nat → ZMod mersenne31Modulus} {aux : QuarticColumn → R} {next : R}
    (accepted : AuxiliaryRowAccepted embed memory processor w aux next) :
    AuxiliaryRowEffects embed memory processor w aux next := by
  obtain ⟨processing,memory,grand⟩ := AuxiliaryProofs.row_balance embed memory processor accepted
  exact ⟨processing,memory,grand⟩

theorem auxiliary_trace_balance {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {w : Nat → Nat → ZMod mersenne31Modulus} {aux : Nat → QuarticColumn → R} {claimed : R}
    (accepted : AuxiliaryTraceAccepted embed memory processor w aux claimed) :
    claimed * (∏ i ∈ Finset.range (constraintsABI.traceLength-1), memoryKeyProduct embed memory (w i) false) =
      ∏ i ∈ Finset.range (constraintsABI.traceLength-1), memoryKeyProduct embed memory (w i) true :=
  AuxiliaryProofs.trace_balance embed memory processor accepted

end Airbender.Blake2Worker.Native
