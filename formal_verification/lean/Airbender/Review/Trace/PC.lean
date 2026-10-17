import Airbender.Proofs.Trace.PC
import Airbender.Proofs.Mersenne31

namespace Airbender.Trace

/-- Public Sail seeds and decoded setup discharge every native incoming PC
    bound/alignment. Imported equations force each RV32 successor, including
    rollover; native state matching bounds the terminal PC. This is a native
    PC-path claim; actual Sail instruction retirement remains separate. -/
theorem public_pc_soundness {trace : Data mersenne31Modulus} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {count logCapacity : Nat}
    (inputs : ImageBoundary trace before cells)
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, row.start.word.Bounded ∧ row.start.word.lo % 4 = 0 ∧
      row.finish.word.Bounded ∧ row.finish.word.toBitVec = row.start.word.toBitVec + 4) ∧
      trace.terminal.word.Bounded :=
  Proofs.image_pc_soundness (by decide) inputs image accepted decoded

end Airbender.Trace
