module
public import Slop.KeccakSplit.Setup.Facts
public import Slop.Arithmetic.ByteAssembly
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/- Field and word facts shared by the three split-worker row proofs. -/

namespace Airbender.Keccak.Split.RowProofs
open Airbender.Trace Airbender.Arithmetic
set_option warningAsError true

theorem char : (2013265921 : ZMod babyBearModulus) = 0 := by decide

/-- The top nibble of a limb is the limb minus three nibbles over 4096. -/
theorem pack_eq {L a b c n : ZMod babyBearModulus}
    (hn : n = -491520 * L + 491520 * a + 7864320 * b + 125829120 * c) :
    L = a + 16 * b + 256 * c + 4096 * n := by
  subst hn
  linear_combination (L - a - 16 * b - 256 * c) * char

/-- The high byte of a limb is the limb minus its low byte over 256. -/
theorem byte_pack {L a n : ZMod babyBearModulus} (hn : n = -7864320 * L + 7864320 * a) :
    L = a + 256 * n := by
  subst hn
  linear_combination (L - a) * char

/-- Four bounded field nibbles recover the canonical sixteen-bit value. -/
theorem value_of_nibbles {x a b c d : ZMod babyBearModulus}
    (ha : a.val < 16) (hb : b.val < 16) (hc : c.val < 16) (hd : d.val < 16)
    (equation : x = a + 16 * b + 256 * c + 4096 * d) :
    x.val = a.val + 16 * (b.val + 16 * (c.val + 16 * d.val)) := by
  have small : a.val + 16 * (b.val + 16 * (c.val + 16 * d.val)) < babyBearModulus :=
    lt_of_lt_of_le (by omega : _ < 65536) (by decide)
  have cast : ((a.val + 16 * (b.val + 16 * (c.val + 16 * d.val)) : Nat) :
      ZMod babyBearModulus) = x := by
    rw [equation]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
  rw [← cast]
  exact ZMod.val_natCast_of_lt small

/-- Four low-to-high bounded chunks form a natural word. -/
def packFourChunks (width : Nat) (values : Fin 4 → Nat) : Nat :=
  values 0 + 2 ^ width * (values 1 + 2 ^ width * (values 2 + 2 ^ width * values 3))

theorem pack_four_xor {width : Nat} (a b : Fin 4 → Nat)
    (ha : ∀ i, a i < 2 ^ width) (hb : ∀ i, b i < 2 ^ width) :
    packFourChunks width (fun i => a i ^^^ b i) = packFourChunks width a ^^^ packFourChunks width b :=
  (xor_of_four_chunks (ha 0) (ha 1) (ha 2) (hb 0) (hb 1) (hb 2) (a₃ := a 3) (b₃ := b 3)).symm

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

theorem token_word {t : MemoryToken babyBearModulus} {a b : Nat} (h : t.value = Nat.pair a b) :
    t.word = ⟨a, b⟩ := by
  simp [MemoryToken.word, h]

theorem bump_small {c : Nat} (h : c < 1600) : bump c < 65536 := by
  dsimp only [bump, encode, Kind.mode]
  split_ifs <;> omega

theorem control_val (index : Fin 361) :
    ((controlAt index.val : ZMod babyBearModulus)).val = controlAt index.val :=
  SetupProofs.val_cast (by have := SetupProofs.controlAt_lt index.isLt; omega)

theorem bump_val (index : Fin 361) :
    ((bump (controlAt index.val) : ZMod babyBearModulus)).val = bump (controlAt index.val) :=
  SetupProofs.val_cast (by have := bump_small (SetupProofs.controlAt_lt index.isLt); omega)

/-- An aligned pointer plus a slot offset does not carry out of the low limb. -/
theorem lane_cell_code {lo hi slot c : Nat} (hlo : lo < 65536) (hhi : hi < 65536)
    (al : lo % 256 = 0) (hs : slot < 31) (hc : c ≤ 4) :
    Nat.pair 1 (Nat.pair (lo + (8 * slot + c)) hi) =
      (Cell.ram (BitVec.ofNat 32 (lo + 65536 * hi) + BitVec.ofNat 32 (8 * slot + c))).addressCode := by
  simp only [Cell.addressCode, Word.ofBitVec, limbBase, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : lo + 65536 * hi < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 8 * slot + c < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : lo + 65536 * hi + (8 * slot + c) < 2 ^ 32)]
  congr 2 <;> omega

/-- The RAM address code of lane half `high` at `slot`, from the native address limbs
    `lo + 8·slot (+4)` and `hi` of an aligned bounded pointer. -/
theorem lane_address_code {base high8 : ZMod babyBearModulus} {slot : Fin 31} (high : Bool)
    (hlo : base.val < 65536) (hhi : high8.val < 65536) (al : base.val % 256 = 0) :
    Nat.pair 1 (Nat.pair (base + 8 * ((slot.val : Nat) : ZMod babyBearModulus) +
        (if high then 4 else 0 : ZMod babyBearModulus)).val high8.val) =
      (Call.laneCell (Word.mk base.val high8.val).toBitVec slot high).addressCode := by
  have hc : (if high then 4 else 0 : Nat) ≤ 4 := by split <;> omega
  have packed : (base + 8 * ((slot.val : Nat) : ZMod babyBearModulus) +
      (if high then 4 else 0 : ZMod babyBearModulus)).val =
      base.val + (8 * slot.val + (if high then 4 else 0 : Nat)) := by
    have cast : ((base.val + (8 * slot.val + (if high then 4 else 0 : Nat)) : Nat) :
        ZMod babyBearModulus) = base + 8 * ((slot.val : Nat) : ZMod babyBearModulus) +
          (if high then 4 else 0 : ZMod babyBearModulus) := by
      cases high <;> push_cast [ZMod.natCast_zmod_val] <;> ring
    rw [← cast]
    exact ZMod.val_natCast_of_lt (lt_of_lt_of_le (by have := slot.isLt; omega : _ < 131072) (by decide))
  rw [packed]
  simp only [Call.laneCell, Word.toBitVec, Word.value, limbBase]
  exact lane_cell_code hlo hhi al slot.isLt hc

end Airbender.Keccak.Split.RowProofs
