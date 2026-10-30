import Airbender.Proofs.Arithmetic.ByteAssembly

namespace Airbender.Arithmetic
set_option warningAsError true

/-- Four low-to-high bounded chunks form a natural word. -/
def packFourChunks (width : Nat) (values : Fin 4 → Nat) : Nat :=
  values 0 + 2 ^ width * (values 1 + 2 ^ width * (values 2 + 2 ^ width * values 3))

/-- Chunkwise XOR preserves the complete packed word. -/
theorem pack_four_xor {width : Nat} (a b : Fin 4 → Nat)
    (ha : ∀ i, a i < 2 ^ width) (hb : ∀ i, b i < 2 ^ width) :
    packFourChunks width (fun i => a i ^^^ b i) = packFourChunks width a ^^^ packFourChunks width b :=
  (xor_of_four_chunks (ha 0) (ha 1) (ha 2) (hb 0) (hb 1) (hb 2) (a₃ := a 3) (b₃ := b 3)).symm

/-- Five bounded chunkwise XOR inputs preserve their complete packed words. -/
theorem pack_four_xor_five {width : Nat} (a b c d e : Fin 4 → Nat)
    (ha : ∀ i, a i < 2 ^ width) (hb : ∀ i, b i < 2 ^ width) (hc : ∀ i, c i < 2 ^ width)
    (hd : ∀ i, d i < 2 ^ width) (he : ∀ i, e i < 2 ^ width) :
    packFourChunks width (fun i => a i ^^^ b i ^^^ c i ^^^ d i ^^^ e i) =
      packFourChunks width a ^^^ packFourChunks width b ^^^ packFourChunks width c ^^^
        packFourChunks width d ^^^ packFourChunks width e := by
  have hab (i : Fin 4) := Nat.xor_lt_two_pow (ha i) (hb i)
  have habc (i : Fin 4) := Nat.xor_lt_two_pow (hab i) (hc i)
  have habcd (i : Fin 4) := Nat.xor_lt_two_pow (habc i) (hd i)
  rw [← pack_four_xor a b ha hb, ← pack_four_xor (fun i => a i ^^^ b i) c hab hc,
    ← pack_four_xor (fun i => a i ^^^ b i ^^^ c i) d habc hd,
    ← pack_four_xor (fun i => a i ^^^ b i ^^^ c i ^^^ d i) e habcd he]

end Airbender.Arithmetic
