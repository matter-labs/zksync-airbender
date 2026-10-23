import Airbender.Proofs.Tables.ImportedBlocks
set_option warningAsError true
set_option Elab.async false

namespace Airbender.Setup.Proofs

theorem checkBlocks_complete (f : Nat → Nat) (blocks : List Block) (start : Nat)
    (rows : ∀ n, n < (blocks.map Block.length).sum →
      getFromBlocks blocks n = some (f (start + n))) :
    checkBlocks f start blocks = true := by
  induction blocks generalizing start with
  | nil => rfl
  | cons b bs ih =>
    rw [checkBlocks_cons_iff]
    refine ⟨?_, ih (start + b.length) ?_⟩
    · intro i
      have value := rows i.val (by simp only [List.map_cons, List.sum_cons]; omega)
      simpa only [getFromBlocks, if_pos i.isLt] using value
    · intro n hn
      have value := rows (b.length + n) (by
        simp only [List.map_cons, List.sum_cons]; omega)
      have skip : ¬ b.length + n < b.length := by omega
      simpa only [getFromBlocks, if_neg skip, Nat.add_sub_cancel_left, Nat.add_assoc] using value

theorem checkBlocks_reindex {f g : Nat → Nat} {blocks : List Block} {start target : Nat}
    (checked : checkBlocks f start blocks = true)
    (same : ∀ n, n < (blocks.map Block.length).sum → f (start + n) = g (target + n)) :
    checkBlocks g target blocks = true := by
  apply checkBlocks_complete
  intro n bound
  rw [checkBlocks_sound f blocks start n checked bound, same n bound]

theorem array_extent_append (left right : Array Block) :
    ((left ++ right).toList.map Block.length).sum =
      (left.toList.map Block.length).sum + (right.toList.map Block.length).sum := by
  rw [Array.toList_append, List.map_append, List.sum_append]

theorem array_extent_join (left right : Array Block) {m n : Nat}
    (hl : (left.toList.map Block.length).sum = m)
    (hr : (right.toList.map Block.length).sum = n) :
    ((left ++ right).toList.map Block.length).sum = m + n :=
  (array_extent_append left right).trans (congrArg₂ Nat.add hl hr)

/-- Reuse a checked byte-XOR column across the three carry cycles. The native
    column shape and extent remain explicit checked premises. -/
theorem cyclic_xor8_check (base native : List Block)
    (head : base = .affine 256 0 1 :: base.tail)
    (shape : native = .affine 1 0 0 :: .affine 255 1 1 ::
      (base.tail ++ (base ++ base)))
    (fullExtent : (native.map Block.length).sum = 196608)
    (baseChecked : checkBlocks (fun n => n / 256 ^^^ n % 256) 0 base = true) :
    checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) 0 native = true := by
  have headExtent : (base.map Block.length).sum =
      256 + (base.tail.map Block.length).sum := by
    conv_lhs => rw [head]
    simp only [List.map_cons, List.sum_cons, Block.length]
  rw [shape] at fullExtent
  simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, Block.length] at fullExtent
  have byte_extent : (base.map Block.length).sum = 65536 := by omega
  have byte_tail_extent : (base.tail.map Block.length).sum = 65280 := by omega
  have chunk (part : Fin 3) :
      checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) (65536 * part.val) base = true := by
    refine checkBlocks_reindex (blocks := base) baseChecked ?_
    intro n bound
    rw [byte_extent] at bound
    fin_cases part <;> congr 1 <;> omega
  have first := chunk 0
  rw [head, checkBlocks_cons_iff] at first
  rw [shape, checkBlocks_cons_iff]
  refine ⟨by decide +kernel, ?_⟩
  rw [checkBlocks_cons_iff]
  refine ⟨by decide +kernel, ?_⟩
  rw [checkBlocks_append_iff, byte_tail_extent]
  refine ⟨first.2, ?_⟩
  rw [checkBlocks_append_iff, byte_extent]
  exact ⟨chunk 1, chunk 2⟩

/-- Reuse a checked seven-bit XOR column in three consecutive carry cycles. -/
theorem cyclic_xor7_check (base native : List Block)
    (shape : native = base ++ (base ++ base))
    (fullExtent : (native.map Block.length).sum = 49152)
    (baseChecked : checkBlocks (fun n => n / 128 ^^^ n % 128) 0 base = true) :
    checkBlocks (fun n => n / 128 % 128 ^^^ n % 128) 0 native = true := by
  rw [shape] at fullExtent
  simp only [List.map_append, List.sum_append] at fullExtent
  have extent : (base.map Block.length).sum = 16384 := by omega
  have chunk (part : Fin 3) :
      checkBlocks (fun n => n / 128 % 128 ^^^ n % 128) (16384 * part.val) base = true := by
    refine checkBlocks_reindex (blocks := base) baseChecked ?_
    intro n bound
    rw [extent] at bound
    fin_cases part <;> congr 1 <;> omega
  rw [shape, checkBlocks_append_iff, extent]
  refine ⟨chunk 0, ?_⟩
  rw [checkBlocks_append_iff, extent]
  exact ⟨chunk 1, chunk 2⟩


end Airbender.Setup.Proofs

