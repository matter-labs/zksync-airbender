import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Keccak.Proofs
open Airbender.Setup
set_option warningAsError true

/-- Pointwise imported-block semantics without enumerating the expanded domain. -/
def BlockRows (f : Nat → Nat) : Nat → List Block → Prop
  | _, [] => True
  | start, block :: rest =>
      (∀ n : Nat, n < block.length → block.get? n = some (f (start + n))) ∧
        BlockRows f (start + block.length) rest

theorem blockRows_sound (f : Nat → Nat) (blocks : List Block) (start n : Nat)
    (rows : BlockRows f start blocks)
    (bound : n < (blocks.map Block.length).sum) :
    getFromBlocks blocks n = some (f (start + n)) := by
  induction blocks generalizing start n with
  | nil => simp at bound
  | cons block rest ih =>
    rcases rows with ⟨first, later⟩
    simp only [List.map_cons, List.sum_cons] at bound
    simp only [getFromBlocks]
    split
    next inside => exact first n inside
    next outside =>
      have result := ih (start + block.length) (n - block.length) later (by omega)
      rw [show start + block.length + (n - block.length) = start + n by omega] at result
      exact result

/-- An interval certificate keeps native lengths in checked constructor fields,
    rather than reducing an entire closed column during proof conversion. -/
inductive BlockCover (f : Nat → Nat) : Nat → Nat → List Block → Prop where
  | nil (position : Nat) : BlockCover f position position []
  | cons (start next finish : Nat) (block : Block) (rest : List Block)
      (ordered : start ≤ next) (length : block.length = next - start)
      (rows : ∀ n : Nat, n < next - start → block.get? n = some (f (start + n)))
      (later : BlockCover f next finish rest) :
      BlockCover f start finish (block :: rest)

theorem blockCover_sound (f : Nat → Nat) {blocks : List Block} {start finish : Nat}
    (cover : BlockCover f start finish blocks) (n : Nat) (bound : n < finish - start) :
    getFromBlocks blocks n = some (f (start + n)) := by
  induction cover generalizing n with
  | nil position => omega
  | cons start next finish block rest ordered length rows later ih =>
    by_cases inside : n < next - start
    · simpa only [getFromBlocks, length, if_pos inside] using rows n inside
    · have result := ih (n - (next - start)) (by omega)
      have position : next + (n - (next - start)) = start + n := by omega
      simpa only [getFromBlocks, length, if_neg inside, position] using result

end Airbender.Keccak.Proofs
