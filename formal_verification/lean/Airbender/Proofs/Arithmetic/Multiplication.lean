import Airbender.Proofs.Arithmetic.Word
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace Airbender.Arithmetic

-- Four 16-bit columns. Products of upper bytes are carried into the next
-- column; the remaining byte/limb products fit the small outer field.
def productColumns (q d r : Word) (carry : Fin 3 → Nat) : Fin 4 → Nat
  | 0 => q.lo % 256 * (d.lo % 256) + q.lo % 256 * (256 * (d.lo / 256)) +
      256 * (q.lo / 256) * (d.lo % 256) + r.lo
  | 1 => q.lo % 256 * (d.hi % 256) + q.lo % 256 * (256 * (d.hi / 256)) +
      q.lo / 256 * (d.lo / 256) + 256 * (q.lo / 256) * (d.hi % 256) +
      q.hi % 256 * (d.lo % 256) + q.hi % 256 * (256 * (d.lo / 256)) +
      256 * (q.hi / 256) * (d.lo % 256) + r.hi + carry 0
  | 2 => q.lo / 256 * (d.hi / 256) + q.hi % 256 * (d.hi % 256) +
      q.hi % 256 * (256 * (d.hi / 256)) + q.hi / 256 * (d.lo / 256) +
      256 * (q.hi / 256) * (d.hi % 256) + carry 1
  | 3 => q.hi / 256 * (d.hi / 256) + carry 2

def productColumnOutputs (low high : Word) (carry : Fin 3 → Nat) : Fin 4 → Nat
  | 0 => low.lo + 65536 * carry 0
  | 1 => low.hi + 65536 * carry 1
  | 2 => high.lo + 65536 * carry 2
  | 3 => high.hi

/-- Lift the byte-column equations before combining them. A single field
    equality for a 64-bit product would lose multiples of the characteristic. -/
theorem product_of_columns {F : Type} [CommRing F] {p : Nat} [CharP F p]
    (hp : 536870912 ≤ p) (q d r low high : Word) (carry : Fin 3 → Nat)
    (qb : q.Bounded) (db : d.Bounded) (rb : r.Bounded)
    (lb : low.Bounded) (hb : high.Bounded)
    (cb : ∀ i, carry i < 8192)
    (equations : ∀ i, (productColumns q d r carry i : F) =
      (productColumnOutputs low high carry i : F)) :
    q.value * d.value + r.value = low.value + wordModulus * high.value := by
  have byte_lt (n : Nat) : n % 256 < 256 := Nat.mod_lt _ (by decide)
  have upper_lt (n : Nat) (hn : n < 65536) : n / 256 < 256 := by omega
  have small_product (a b : Nat) (ha : a < 256) (hb : b < 256) :
      a * b ≤ 65025 := Nat.mul_le_mul (by omega : a ≤ 255) (by omega : b ≤ 255)
  have limb_product (a b : Nat) (ha : a < 256) (hb : b < 256) :
      a * (256 * b) ≤ 16646400 ∧ 256 * a * b ≤ 16646400 := by
    have bound := Nat.mul_le_mul_left 256 (small_product a b ha hb)
    constructor <;> convert bound using 1 <;> ring
  have q0 := upper_lt q.lo qb.1
  have q1 := upper_lt q.hi qb.2
  have d0 := upper_lt d.lo db.1
  have d1 := upper_lt d.hi db.2
  have p00 := small_product (q.lo % 256) (d.lo % 256) (byte_lt _) (byte_lt _)
  have p01 := limb_product (q.lo % 256) (d.lo / 256) (byte_lt _) d0
  have p02 := limb_product (q.lo / 256) (d.lo % 256) q0 (byte_lt _)
  have p10 := small_product (q.lo % 256) (d.hi % 256) (byte_lt _) (byte_lt _)
  have p11 := limb_product (q.lo % 256) (d.hi / 256) (byte_lt _) d1
  have p12 := small_product (q.lo / 256) (d.lo / 256) q0 d0
  have p13 := limb_product (q.lo / 256) (d.hi % 256) q0 (byte_lt _)
  have p14 := small_product (q.hi % 256) (d.lo % 256) (byte_lt _) (byte_lt _)
  have p15 := limb_product (q.hi % 256) (d.lo / 256) (byte_lt _) d0
  have p16 := limb_product (q.hi / 256) (d.lo % 256) q1 (byte_lt _)
  have p20 := small_product (q.lo / 256) (d.hi / 256) q0 d1
  have p21 := small_product (q.hi % 256) (d.hi % 256) (byte_lt _) (byte_lt _)
  have p22 := limb_product (q.hi % 256) (d.hi / 256) (byte_lt _) d1
  have p23 := small_product (q.hi / 256) (d.lo / 256) q1 d0
  have p24 := limb_product (q.hi / 256) (d.hi % 256) q1 (byte_lt _)
  have p30 := small_product (q.hi / 256) (d.hi / 256) q1 d1
  have c0 := cb 0
  have c1 := cb 1
  have c2 := cb 2
  have columns : ∀ i, productColumns q d r carry i = productColumnOutputs low high carry i := by
    intro i
    apply bounded_nat_eq (F := F) (p := p) _ _ (equations i)
    · fin_cases i <;> dsimp [productColumns] <;>
        unfold Word.Bounded limbBase at rb <;> omega
    · fin_cases i <;> dsimp [productColumnOutputs] <;>
        unfold Word.Bounded limbBase at lb hb <;> omega
  have e0 := columns 0
  have e1 := columns 1
  have e2 := columns 2
  have e3 := columns 3
  dsimp [productColumns, productColumnOutputs] at e0 e1 e2 e3
  have qlo := Nat.mod_add_div q.lo 256
  have qhi := Nat.mod_add_div q.hi 256
  have dlo := Nat.mod_add_div d.lo 256
  have dhi := Nat.mod_add_div d.hi 256
  rw [Word.value, Word.value, Word.value, Word.value, Word.value]
  unfold limbBase wordModulus
  rw [← qlo, ← qhi, ← dlo, ← dhi]
  nlinarith only [e0, e1, e2, e3]

end Airbender.Arithmetic
