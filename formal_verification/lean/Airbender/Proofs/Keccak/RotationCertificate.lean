import Airbender.Review.Circuits.Keccak.Tables.FixedData
import Airbender.Proofs.Keccak.RotationBlocks
import Airbender.Proofs.Keccak.RotationTemplates

namespace Airbender.Keccak.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 131072

def rotationHigh (key : Nat) : Nat :=
  (key % 65536) / 2 ^ (16 - key / 65536)
def rotationLow (key : Nat) : Nat :=
  ((key % 65536) * 2 ^ (key / 65536)) % 65536

private theorem affine_nat (length first : Nat) (step : Int) (n : Nat)
    (positive : 0 ≤ step) :
    Block.get? (.affine length first step) n =
      if n < length then some (first + step.toNat * n) else none := by
  by_cases bound : n < length
  · simp only [Block.get?, Block.length, if_pos bound]
    have nonneg : 0 ≤ (first : Int) + step * n :=
      add_nonneg (Int.natCast_nonneg first) (mul_nonneg positive (Int.natCast_nonneg n))
    simp only [if_pos nonneg]
    rw [Int.toNat_add (Int.natCast_nonneg first)
      (mul_nonneg positive (Int.natCast_nonneg n)),
      Int.toNat_mul positive (Int.natCast_nonneg n)]
    simp
  · simp [Block.get?, Block.length, bound]
private theorem periodic_nat (count : Nat) (stride : Int) (values : Array Nat) (n : Nat)
    (positive : 0 ≤ stride) :
    Block.get? (.periodic count stride values) n =
      if n < count * values.size then
        some ((values[n % values.size]?.getD 0) + stride.toNat * (n / values.size)) else none := by
  by_cases bound : n < count * values.size
  · simp only [Block.get?, Block.length, if_pos bound]
    simp only [← Int.natCast_ediv]
    have nonneg : 0 ≤ ((values[n % values.size]?.getD 0 : Nat) : Int) +
        stride * ((n / values.size : Nat) : Int) :=
      add_nonneg (Int.natCast_nonneg _) (mul_nonneg positive (Int.natCast_nonneg _))
    simp only [if_pos nonneg]
    rw [Int.toNat_add (Int.natCast_nonneg _)
      (mul_nonneg positive (Int.natCast_nonneg _)),
      Int.toNat_mul positive (Int.natCast_nonneg _)]
    simp only [Int.toNat_natCast]
  · simp [Block.get?, Block.length, bound]



private theorem affine_inrange (length first : Nat) (step : Int) (n : Nat)
    (positive : 0 ≤ step) (bound : n < length) :
    Block.get? (.affine length first step) n = some (first + step.toNat * n) := by
  rw [affine_nat _ _ _ _ positive, if_pos bound]

private theorem high_periodic_inrange (count size n : Nat) (bound : n < count * size) :
    Block.get? (.periodic count 1 (Array.replicate size 0)) n = some (n / size) := by
  have positive : 0 < size := by
    by_contra h
    have zero : size = 0 := by omega
    simp [zero] at bound
  have residue := Nat.mod_lt n positive
  simp only [periodic_nat _ _ _ _ (by decide : (0 : Int) ≤ 1), Array.size_replicate,
    if_pos bound, Array.getElem?_replicate, if_pos residue, Option.getD_some,
    Int.toNat_one, Nat.one_mul, Nat.zero_add]

private theorem low_array_inrange (count size step n : Nat) (values : Array Nat)
    (length : values.size = size)
    (contents : ∀ index : Nat, index < size → values[index]? = some (step * index))
    (bound : n < count * size) :
    Block.get? (.periodic count 0 values) n = some (step * (n % size)) := by
  have positive : 0 < size := by
    by_contra h
    have zero : size = 0 := by omega
    simp [zero] at bound
  rw [periodic_nat _ _ _ _ (by decide : (0 : Int) ≤ 0)]
  simp only [length, if_pos bound, contents _ (Nat.mod_lt _ positive),
    Option.getD_some, Int.toNat_zero, Nat.zero_mul, Nat.add_zero]

macro "keccak_rotation_block " meaning:ident start:num shift:num : tactic =>
  `(tactic|
    (intro n bound
     have quotient : ($start + n) / 65536 = $shift := by omega
     unfold $meaning
     simp only [quotient, Nat.reducePow, Nat.reduceSub]
     simp (disch := omega) [affine_inrange, high_periodic_inrange] <;> omega))

macro "keccak_rotation_native " values:ident sizeProof:ident getProof:ident
    start:num shift:num count:num size:num step:num : tactic =>
  `(tactic|
    (intro n bound
     have quotient : ($start + n) / 65536 = $shift := by omega
     have native : Block.get? (.periodic $count (Int.ofNat 0) $values) n =
         some ($step * (n % $size)) :=
       low_array_inrange $count $size $step n $values $sizeProof $getProof (by omega)
     rewrite [native]
     clear native
     simp only [rotationLow, quotient, Nat.reducePow]
     exact congrArg some (show $step * (n % $size) =
       ((($start + n) % 65536) * $step) % 65536 from by omega)))

private theorem high_rows :
    BlockRows rotationHigh 0 rotationData.columns[1].blocks.toList := by
  dsimp only [rotationData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append,
    BlockRows, and_true, Block.length, Array.size_replicate, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  · intro n bound
    by_cases before : n < 65536
    · have quotient : n / 65536 = 0 := by omega
      simp only [rotationHigh, Nat.zero_add, quotient, Nat.reduceSub, Nat.reducePow]
      simp (disch := omega) [affine_inrange]
    · have quotient : n / 65536 = 1 := by omega
      simp only [rotationHigh, Nat.zero_add, quotient, Nat.reduceSub, Nat.reducePow]
      simp (disch := omega) [affine_inrange]
      omega
  · keccak_rotation_block rotationHigh 98304 1
  · keccak_rotation_block rotationHigh 131072 2
  · keccak_rotation_block rotationHigh 147456 2
  · keccak_rotation_block rotationHigh 163840 2
  · keccak_rotation_block rotationHigh 180224 2
  · keccak_rotation_block rotationHigh 196608 3
  · keccak_rotation_block rotationHigh 204800 3
  · keccak_rotation_block rotationHigh 212992 3
  · keccak_rotation_block rotationHigh 221184 3
  · keccak_rotation_block rotationHigh 229376 3
  · keccak_rotation_block rotationHigh 237568 3
  · keccak_rotation_block rotationHigh 245760 3
  · keccak_rotation_block rotationHigh 253952 3
  · keccak_rotation_block rotationHigh 262144 4
  · keccak_rotation_block rotationHigh 266240 4
  · keccak_rotation_block rotationHigh 270336 4
  · keccak_rotation_block rotationHigh 274432 4
  · keccak_rotation_block rotationHigh 278528 4
  · keccak_rotation_block rotationHigh 282624 4
  · keccak_rotation_block rotationHigh 286720 4
  · keccak_rotation_block rotationHigh 290816 4
  · keccak_rotation_block rotationHigh 294912 4
  · keccak_rotation_block rotationHigh 299008 4
  · keccak_rotation_block rotationHigh 303104 4
  · keccak_rotation_block rotationHigh 307200 4
  · keccak_rotation_block rotationHigh 311296 4
  · keccak_rotation_block rotationHigh 315392 4
  · keccak_rotation_block rotationHigh 319488 4
  · keccak_rotation_block rotationHigh 323584 4
  · keccak_rotation_block rotationHigh 327680 5
  · keccak_rotation_block rotationHigh 329728 5
  · keccak_rotation_block rotationHigh 331776 5
  · keccak_rotation_block rotationHigh 333824 5
  · keccak_rotation_block rotationHigh 335872 5
  · keccak_rotation_block rotationHigh 337920 5
  · keccak_rotation_block rotationHigh 339968 5
  · keccak_rotation_block rotationHigh 342016 5
  · keccak_rotation_block rotationHigh 344064 5
  · keccak_rotation_block rotationHigh 346112 5
  · keccak_rotation_block rotationHigh 348160 5
  · keccak_rotation_block rotationHigh 350208 5
  · keccak_rotation_block rotationHigh 352256 5
  · keccak_rotation_block rotationHigh 354304 5
  · keccak_rotation_block rotationHigh 356352 5
  · keccak_rotation_block rotationHigh 358400 5
  · keccak_rotation_block rotationHigh 360448 5
  · keccak_rotation_block rotationHigh 362496 5
  · keccak_rotation_block rotationHigh 364544 5
  · keccak_rotation_block rotationHigh 366592 5
  · keccak_rotation_block rotationHigh 368640 5
  · keccak_rotation_block rotationHigh 370688 5
  · keccak_rotation_block rotationHigh 372736 5
  · keccak_rotation_block rotationHigh 374784 5
  · keccak_rotation_block rotationHigh 376832 5
  · keccak_rotation_block rotationHigh 378880 5
  · keccak_rotation_block rotationHigh 380928 5
  · keccak_rotation_block rotationHigh 382976 5
  · keccak_rotation_block rotationHigh 385024 5
  · keccak_rotation_block rotationHigh 387072 5
  · keccak_rotation_block rotationHigh 389120 5
  · keccak_rotation_block rotationHigh 391168 5
  · keccak_rotation_block rotationHigh 393216 6
  · keccak_rotation_block rotationHigh 458752 7
  · keccak_rotation_block rotationHigh 524288 8
  · keccak_rotation_block rotationHigh 589824 9
  · keccak_rotation_block rotationHigh 655360 10
  · keccak_rotation_block rotationHigh 720896 11
  · keccak_rotation_block rotationHigh 786432 12
  · keccak_rotation_block rotationHigh 851968 13
  · keccak_rotation_block rotationHigh 917504 14
  · keccak_rotation_block rotationHigh 983040 15

private theorem high_covered :
    ((rotationData.columns[1]).blocks.toList.map Block.length).sum = 1048576 := by
  dsimp only [rotationData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Block.length, Array.size_replicate, Nat.reduceAdd, Nat.reduceMul]

/-- Exact imported high piece for every native packed key. -/
theorem rotation_high_column (n : Nat) (bound : n < 1048576) :
    rotationData.columns[1].get? n = some (rotationHigh n) := by
  have result := blockRows_sound _ _ 0 n high_rows
    (by simpa only [high_covered] using bound)
  simpa only [Column.get?, Nat.zero_add] using result

private theorem low_tail0 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 64 (Int.ofNat 0) rotationTemplates0) n =
      some (rotationLow (393216 + n)) := by
  keccak_rotation_native rotationTemplates0 rotationTemplates0_size rotationTemplates0_get 393216 6 64 1024 64

private theorem low_tail1 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 128 (Int.ofNat 0) rotationTemplates1) n =
      some (rotationLow (458752 + n)) := by
  keccak_rotation_native rotationTemplates1 rotationTemplates1_size rotationTemplates1_get 458752 7 128 512 128

private theorem low_tail2 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 256 (Int.ofNat 0) rotationTemplates2) n =
      some (rotationLow (524288 + n)) := by
  keccak_rotation_native rotationTemplates2 rotationTemplates2_size rotationTemplates2_get 524288 8 256 256 256

private theorem low_tail3 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 512 (Int.ofNat 0) rotationTemplates3) n =
      some (rotationLow (589824 + n)) := by
  keccak_rotation_native rotationTemplates3 rotationTemplates3_size rotationTemplates3_get 589824 9 512 128 512

private theorem low_tail4 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 1024 (Int.ofNat 0) rotationTemplates4) n =
      some (rotationLow (655360 + n)) := by
  keccak_rotation_native rotationTemplates4 rotationTemplates4_size rotationTemplates4_get 655360 10 1024 64 1024

private theorem low_tail5 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 2048 (Int.ofNat 0) rotationTemplates5) n =
      some (rotationLow (720896 + n)) := by
  keccak_rotation_native rotationTemplates5 rotationTemplates5_size rotationTemplates5_get 720896 11 2048 32 2048

private theorem low_tail6 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 4096 (Int.ofNat 0) rotationTemplates6) n =
      some (rotationLow (786432 + n)) := by
  keccak_rotation_native rotationTemplates6 rotationTemplates6_size rotationTemplates6_get 786432 12 4096 16 4096

private theorem low_tail7 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 8192 (Int.ofNat 0) rotationTemplates7) n =
      some (rotationLow (851968 + n)) := by
  keccak_rotation_native rotationTemplates7 rotationTemplates7_size rotationTemplates7_get 851968 13 8192 8 8192

private theorem low_tail8 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 16384 (Int.ofNat 0) rotationTemplates8) n =
      some (rotationLow (917504 + n)) := by
  keccak_rotation_native rotationTemplates8 rotationTemplates8_size rotationTemplates8_get 917504 14 16384 4 16384

private theorem low_tail9 : ∀ n : Nat, n < 65536 →
    Block.get? (.periodic 32768 (Int.ofNat 0) rotationTemplates9) n =
      some (rotationLow (983040 + n)) := by
  keccak_rotation_native rotationTemplates9 rotationTemplates9_size rotationTemplates9_get 983040 15 32768 2 32768

private theorem periodic_length_eq (count size : Nat) (stride : Int) (values : Array Nat)
    (h : values.size = size) : (.periodic count stride values : Block).length = count * size := by
  exact congrArg (Nat.mul count) h
private theorem low_length0 : (.periodic 64 (Int.ofNat 0) rotationTemplates0 : Block).length = 65536 := by
  exact periodic_length_eq 64 1024 (Int.ofNat 0) rotationTemplates0 rotationTemplates0_size
private theorem low_length1 : (.periodic 128 (Int.ofNat 0) rotationTemplates1 : Block).length = 65536 := by
  exact periodic_length_eq 128 512 (Int.ofNat 0) rotationTemplates1 rotationTemplates1_size
private theorem low_length2 : (.periodic 256 (Int.ofNat 0) rotationTemplates2 : Block).length = 65536 := by
  exact periodic_length_eq 256 256 (Int.ofNat 0) rotationTemplates2 rotationTemplates2_size
private theorem low_length3 : (.periodic 512 (Int.ofNat 0) rotationTemplates3 : Block).length = 65536 := by
  exact periodic_length_eq 512 128 (Int.ofNat 0) rotationTemplates3 rotationTemplates3_size
private theorem low_length4 : (.periodic 1024 (Int.ofNat 0) rotationTemplates4 : Block).length = 65536 := by
  exact periodic_length_eq 1024 64 (Int.ofNat 0) rotationTemplates4 rotationTemplates4_size
private theorem low_length5 : (.periodic 2048 (Int.ofNat 0) rotationTemplates5 : Block).length = 65536 := by
  exact periodic_length_eq 2048 32 (Int.ofNat 0) rotationTemplates5 rotationTemplates5_size
private theorem low_length6 : (.periodic 4096 (Int.ofNat 0) rotationTemplates6 : Block).length = 65536 := by
  exact periodic_length_eq 4096 16 (Int.ofNat 0) rotationTemplates6 rotationTemplates6_size
private theorem low_length7 : (.periodic 8192 (Int.ofNat 0) rotationTemplates7 : Block).length = 65536 := by
  exact periodic_length_eq 8192 8 (Int.ofNat 0) rotationTemplates7 rotationTemplates7_size
private theorem low_length8 : (.periodic 16384 (Int.ofNat 0) rotationTemplates8 : Block).length = 65536 := by
  exact periodic_length_eq 16384 4 (Int.ofNat 0) rotationTemplates8 rotationTemplates8_size
private theorem low_length9 : (.periodic 32768 (Int.ofNat 0) rotationTemplates9 : Block).length = 65536 := by
  exact periodic_length_eq 32768 2 (Int.ofNat 0) rotationTemplates9 rotationTemplates9_size

macro "keccak_cover_affine " start:num finishBlock:num shift:num : tactic =>
  `(tactic|
    (apply BlockCover.cons (next := $finishBlock)
     · decide
     · rfl
     · keccak_rotation_block rotationLow $start $shift))

macro "keccak_cover_periodic " finishBlock:num sizeProof:ident rowsProof:ident : tactic =>
  `(tactic|
    (apply BlockCover.cons (next := $finishBlock)
     · decide
     · exact $sizeProof
     · exact $rowsProof))

private theorem low_cover :
    BlockCover rotationLow 0 1048576 rotationData.columns[2].blocks.toList := by
  dsimp only [rotationData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append]
  keccak_cover_affine 0 65536 0
  keccak_cover_affine 65536 98304 1
  keccak_cover_affine 98304 131072 1
  keccak_cover_affine 131072 147456 2
  keccak_cover_affine 147456 163840 2
  keccak_cover_affine 163840 180224 2
  keccak_cover_affine 180224 196608 2
  keccak_cover_affine 196608 204800 3
  keccak_cover_affine 204800 212992 3
  keccak_cover_affine 212992 221184 3
  keccak_cover_affine 221184 229376 3
  keccak_cover_affine 229376 237568 3
  keccak_cover_affine 237568 245760 3
  keccak_cover_affine 245760 253952 3
  keccak_cover_affine 253952 262144 3
  keccak_cover_affine 262144 266240 4
  keccak_cover_affine 266240 270336 4
  keccak_cover_affine 270336 274432 4
  keccak_cover_affine 274432 278528 4
  keccak_cover_affine 278528 282624 4
  keccak_cover_affine 282624 286720 4
  keccak_cover_affine 286720 290816 4
  keccak_cover_affine 290816 294912 4
  keccak_cover_affine 294912 299008 4
  keccak_cover_affine 299008 303104 4
  keccak_cover_affine 303104 307200 4
  keccak_cover_affine 307200 311296 4
  keccak_cover_affine 311296 315392 4
  keccak_cover_affine 315392 319488 4
  keccak_cover_affine 319488 323584 4
  keccak_cover_affine 323584 327680 4
  keccak_cover_affine 327680 329728 5
  keccak_cover_affine 329728 331776 5
  keccak_cover_affine 331776 333824 5
  keccak_cover_affine 333824 335872 5
  keccak_cover_affine 335872 337920 5
  keccak_cover_affine 337920 339968 5
  keccak_cover_affine 339968 342016 5
  keccak_cover_affine 342016 344064 5
  keccak_cover_affine 344064 346112 5
  keccak_cover_affine 346112 348160 5
  keccak_cover_affine 348160 350208 5
  keccak_cover_affine 350208 352256 5
  keccak_cover_affine 352256 354304 5
  keccak_cover_affine 354304 356352 5
  keccak_cover_affine 356352 358400 5
  keccak_cover_affine 358400 360448 5
  keccak_cover_affine 360448 362496 5
  keccak_cover_affine 362496 364544 5
  keccak_cover_affine 364544 366592 5
  keccak_cover_affine 366592 368640 5
  keccak_cover_affine 368640 370688 5
  keccak_cover_affine 370688 372736 5
  keccak_cover_affine 372736 374784 5
  keccak_cover_affine 374784 376832 5
  keccak_cover_affine 376832 378880 5
  keccak_cover_affine 378880 380928 5
  keccak_cover_affine 380928 382976 5
  keccak_cover_affine 382976 385024 5
  keccak_cover_affine 385024 387072 5
  keccak_cover_affine 387072 389120 5
  keccak_cover_affine 389120 391168 5
  keccak_cover_affine 391168 393216 5
  keccak_cover_periodic 458752 low_length0 low_tail0
  keccak_cover_periodic 524288 low_length1 low_tail1
  keccak_cover_periodic 589824 low_length2 low_tail2
  keccak_cover_periodic 655360 low_length3 low_tail3
  keccak_cover_periodic 720896 low_length4 low_tail4
  keccak_cover_periodic 786432 low_length5 low_tail5
  keccak_cover_periodic 851968 low_length6 low_tail6
  keccak_cover_periodic 917504 low_length7 low_tail7
  keccak_cover_periodic 983040 low_length8 low_tail8
  keccak_cover_periodic 1048576 low_length9 low_tail9
  exact BlockCover.nil _

/-- Exact imported low piece for every native packed key. -/
theorem rotation_low_column (n : Nat) (bound : n < 1048576) :
    rotationData.columns[2].get? n = some (rotationLow n) := by
  have result := blockCover_sound rotationLow low_cover n
    (by simpa only [Nat.sub_zero] using bound)
  simpa only [Column.get?, Nat.zero_add] using result

end Airbender.Keccak.Proofs
