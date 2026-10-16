import Airbender.Review.Circuits.Keccak.Tables.RotationData
import Airbender.Proofs.Tables.ImportedBlocks
import Mathlib.Tactic.FinCases
namespace Airbender.Keccak.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000
private theorem literal_size {α : Type*} (values : List α) :
    (Array.mk values).size = values.length := rfl

theorem rotationTemplates0_size : rotationTemplates0.size = 1024 := by
  dsimp only [rotationTemplates0]
  simp only [raw_size_append, literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks0 : ∀ high low : Fin 32,
    32 * high.val + low.val < 1024 →
      rotationTemplates0[32 * high.val + low.val]? = some (64 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates0]
  all_goals simp only [raw_get_append, raw_size_append, literal_size,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates0_get (index : Nat) (bound : index < 1024) :
    rotationTemplates0[index]? = some (64 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 1024 →
      rotationTemplates0[32 * (index / 32) + index % 32]? =
        some (64 * (32 * (index / 32) + index % 32)) :=
    checks0 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

theorem rotationTemplates1_size : rotationTemplates1.size = 512 := by
  dsimp only [rotationTemplates1]
  simp only [raw_size_append, literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks1 : ∀ high low : Fin 32,
    32 * high.val + low.val < 512 →
      rotationTemplates1[32 * high.val + low.val]? = some (128 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates1]
  all_goals simp only [raw_get_append, raw_size_append, literal_size,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates1_get (index : Nat) (bound : index < 512) :
    rotationTemplates1[index]? = some (128 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 512 →
      rotationTemplates1[32 * (index / 32) + index % 32]? =
        some (128 * (32 * (index / 32) + index % 32)) :=
    checks1 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

theorem rotationTemplates2_size : rotationTemplates2.size = 256 := by
  dsimp only [rotationTemplates2]
  simp only [raw_size_append, literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks2 : ∀ high low : Fin 32,
    32 * high.val + low.val < 256 →
      rotationTemplates2[32 * high.val + low.val]? = some (256 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates2]
  all_goals simp only [raw_get_append, raw_size_append, literal_size,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates2_get (index : Nat) (bound : index < 256) :
    rotationTemplates2[index]? = some (256 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 256 →
      rotationTemplates2[32 * (index / 32) + index % 32]? =
        some (256 * (32 * (index / 32) + index % 32)) :=
    checks2 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

theorem rotationTemplates3_size : rotationTemplates3.size = 128 := by
  dsimp only [rotationTemplates3]
  simp only [raw_size_append, literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks3 : ∀ high low : Fin 32,
    32 * high.val + low.val < 128 →
      rotationTemplates3[32 * high.val + low.val]? = some (512 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates3]
  all_goals simp only [raw_get_append, literal_size, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates3_get (index : Nat) (bound : index < 128) :
    rotationTemplates3[index]? = some (512 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 128 →
      rotationTemplates3[32 * (index / 32) + index % 32]? =
        some (512 * (32 * (index / 32) + index % 32)) :=
    checks3 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

theorem rotationTemplates4_size : rotationTemplates4.size = 64 := by
  dsimp only [rotationTemplates4]
  simp only [literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks4 : ∀ high low : Fin 32,
    32 * high.val + low.val < 64 →
      rotationTemplates4[32 * high.val + low.val]? = some (1024 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates4]
  all_goals simp only [Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates4_get (index : Nat) (bound : index < 64) :
    rotationTemplates4[index]? = some (1024 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 64 →
      rotationTemplates4[32 * (index / 32) + index % 32]? =
        some (1024 * (32 * (index / 32) + index % 32)) :=
    checks4 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

theorem rotationTemplates5_size : rotationTemplates5.size = 32 := by
  dsimp only [rotationTemplates5]
  simp only [literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks5 : ∀ high low : Fin 32,
    32 * high.val + low.val < 32 →
      rotationTemplates5[32 * high.val + low.val]? = some (2048 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates5]
  all_goals simp only [Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates5_get (index : Nat) (bound : index < 32) :
    rotationTemplates5[index]? = some (2048 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 32 →
      rotationTemplates5[32 * (index / 32) + index % 32]? =
        some (2048 * (32 * (index / 32) + index % 32)) :=
    checks5 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

theorem rotationTemplates6_size : rotationTemplates6.size = 16 := by
  dsimp only [rotationTemplates6]
  simp only [literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks6 : ∀ high low : Fin 32,
    32 * high.val + low.val < 16 →
      rotationTemplates6[32 * high.val + low.val]? = some (4096 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates6]
  all_goals simp only [Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates6_get (index : Nat) (bound : index < 16) :
    rotationTemplates6[index]? = some (4096 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 16 →
      rotationTemplates6[32 * (index / 32) + index % 32]? =
        some (4096 * (32 * (index / 32) + index % 32)) :=
    checks6 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

theorem rotationTemplates7_size : rotationTemplates7.size = 8 := by
  dsimp only [rotationTemplates7]
  simp only [literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks7 : ∀ high low : Fin 32,
    32 * high.val + low.val < 8 →
      rotationTemplates7[32 * high.val + low.val]? = some (8192 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates7]
  all_goals simp only [Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates7_get (index : Nat) (bound : index < 8) :
    rotationTemplates7[index]? = some (8192 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 8 →
      rotationTemplates7[32 * (index / 32) + index % 32]? =
        some (8192 * (32 * (index / 32) + index % 32)) :=
    checks7 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

theorem rotationTemplates8_size : rotationTemplates8.size = 4 := by
  dsimp only [rotationTemplates8]
  simp only [literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks8 : ∀ high low : Fin 32,
    32 * high.val + low.val < 4 →
      rotationTemplates8[32 * high.val + low.val]? = some (16384 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates8]
  all_goals simp only [Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates8_get (index : Nat) (bound : index < 4) :
    rotationTemplates8[index]? = some (16384 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 4 →
      rotationTemplates8[32 * (index / 32) + index % 32]? =
        some (16384 * (32 * (index / 32) + index % 32)) :=
    checks8 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

theorem rotationTemplates9_size : rotationTemplates9.size = 2 := by
  dsimp only [rotationTemplates9]
  simp only [literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

private theorem checks9 : ∀ high low : Fin 32,
    32 * high.val + low.val < 2 →
      rotationTemplates9[32 * high.val + low.val]? = some (32768 * (32 * high.val + low.val)) := by
  intro high
  fin_cases high
  all_goals dsimp only [rotationTemplates9]
  all_goals simp only [Nat.reduceMul, List.getElem?_toArray]
  all_goals decide +kernel

theorem rotationTemplates9_get (index : Nat) (bound : index < 2) :
    rotationTemplates9[index]? = some (32768 * index) := by
  have high : index / 32 < 32 := by omega
  have value : 32 * (index / 32) + index % 32 < 2 →
      rotationTemplates9[32 * (index / 32) + index % 32]? =
        some (32768 * (32 * (index / 32) + index % 32)) :=
    checks9 ⟨index / 32, high⟩ ⟨index % 32, Nat.mod_lt _ (by decide)⟩
  rw [show 32 * (index / 32) + index % 32 = index by omega] at value
  exact value bound

end Airbender.Keccak.Proofs
