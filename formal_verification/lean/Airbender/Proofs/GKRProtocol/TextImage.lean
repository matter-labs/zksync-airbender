import Airbender.Review.Helpers.Memory.TextImage

namespace Airbender.Trace.ROM.Proofs

theorem words_of_text_image (before : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (image : TextImage before text)
    (index : Fin text.length) : words before index.val = text[index.val] := by
  simp [words, image index]

end Airbender.Trace.ROM.Proofs
