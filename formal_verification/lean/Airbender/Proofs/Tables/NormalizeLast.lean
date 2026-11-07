import Airbender.Review.Helpers.Tables.NormalizeLast

namespace Airbender.Verification.NormalizeLastProofs
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem ordinary {R : Type} [AddCommGroup R] {size i : Nat} (rows : Nat → R) (bound : i < size-1) :
    normalizeLast size rows i = rows i := if_neg (Nat.ne_of_lt bound)

theorem terminal {R : Type} [AddCommGroup R] (size : Nat) (rows : Nat → R) :
    normalizeLast size rows (size-1) = -(∑ i ∈ Finset.range (size-1), rows i) := if_pos rfl

theorem domain_sum {R : Type} [AddCommGroup R] {size : Nat} (positive : 0 < size) (rows : Nat → R) :
    (∑ i ∈ Finset.range size, normalizeLast size rows i) = 0 := by
  have prefixSum : (∑ i ∈ Finset.range (size-1), normalizeLast size rows i) =
      ∑ i ∈ Finset.range (size-1), rows i := by
    apply Finset.sum_congr rfl
    intro i member
    exact ordinary rows (Finset.mem_range.mp member)
  calc
    _ = ∑ i ∈ Finset.range ((size-1)+1), normalizeLast size rows i := by
      rw [Nat.sub_add_cancel positive]
    _ = (∑ i ∈ Finset.range (size-1), normalizeLast size rows i) + normalizeLast size rows (size-1) :=
      Finset.sum_range_succ _ _
    _ = 0 := by rw [prefixSum,terminal,add_neg_cancel]

theorem vector_column {R : Type} [AddCommGroup R] {width : Nat}
    (size : Nat) (rows : Nat → Vector R width) (i : Nat) (column : Fin width) :
    (normalizeRows size rows i)[column.val] = normalizeLast size (fun j => (rows j)[column.val]) i := by
  simp only [normalizeRows,Vector.getElem_ofFn]

theorem vector_terminal {R : Type} [AddCommGroup R] {width : Nat}
    (size : Nat) (rows : Nat → Vector R width) (column : Fin width) :
    (normalizeRows size rows (size-1))[column.val] = -(∑ i ∈ Finset.range (size-1), (rows i)[column.val]) := by
  rw [vector_column,terminal]

theorem vector_sum {R : Type} [AddCommGroup R] {width size : Nat} (positive : 0 < size)
    (rows : Nat → Vector R width) (column : Fin width) :
    (∑ i ∈ Finset.range size, (normalizeRows size rows i)[column.val]) = 0 := by
  simp_rw [vector_column]
  exact domain_sum positive _

theorem vector_constant_terminal {R : Type} [AddCommGroup R] {width : Nat}
    (size : Nat) (rows : Nat → Vector R width) (column : Fin width) (value : R)
    (constant : ∀ i, (rows i)[column.val] = value) :
    (normalizeRows size rows (size-1))[column.val] = -((size-1) • value) := by
  rw [vector_terminal]
  simp_rw [constant]
  rw [Finset.sum_const,Finset.card_range]
end Airbender.Verification.NormalizeLastProofs
