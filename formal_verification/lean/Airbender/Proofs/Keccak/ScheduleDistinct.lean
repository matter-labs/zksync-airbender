import Airbender.Review.Trace.Workers.Keccak.Call
import Airbender.Review.Circuits.Keccak.Tables.Controller
import Mathlib.Data.List.Nodup

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private abbrev scheduledDistinct (i : Fin 649) : Prop :=
  ((Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048))).toList).Nodup

private def scheduledChunk (base width : Nat) (fits : base + width ≤ 649)
    (i : Fin width) : Fin 649 := ⟨base + i.val, by omega⟩

private theorem distinct0 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 0 64 (by decide) i) := by decide +kernel
private theorem distinct1 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 64 64 (by decide) i) := by decide +kernel
private theorem distinct2 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 128 64 (by decide) i) := by decide +kernel
private theorem distinct3 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 192 64 (by decide) i) := by decide +kernel
private theorem distinct4 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 256 64 (by decide) i) := by decide +kernel
private theorem distinct5 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 320 64 (by decide) i) := by decide +kernel
private theorem distinct6 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 384 64 (by decide) i) := by decide +kernel
private theorem distinct7 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 448 64 (by decide) i) := by decide +kernel
private theorem distinct8 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 512 64 (by decide) i) := by decide +kernel
private theorem distinct9 : ∀ i : Fin 64,
    scheduledDistinct (scheduledChunk 576 64 (by decide) i) := by decide +kernel
private theorem distinct10 : ∀ i : Fin 9,
    scheduledDistinct (scheduledChunk 640 9 (by decide) i) := by decide +kernel

theorem scheduled_lane_indices_distinct (i : Fin 649) :
    ((Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨i.val, by omega⟩).packed + 2048))).toList).Nodup := by
  change scheduledDistinct i
  have bound := i.isLt
  by_cases h0 : i.val < 64
  · simpa only [scheduledChunk, Nat.zero_add] using distinct0 ⟨i.val, h0⟩
  by_cases h1 : i.val < 128
  · simpa only [scheduledChunk, show 64 + (i.val - 64) = i.val by omega] using
      distinct1 ⟨i.val - 64, by omega⟩
  by_cases h2 : i.val < 192
  · simpa only [scheduledChunk, show 128 + (i.val - 128) = i.val by omega] using
      distinct2 ⟨i.val - 128, by omega⟩
  by_cases h3 : i.val < 256
  · simpa only [scheduledChunk, show 192 + (i.val - 192) = i.val by omega] using
      distinct3 ⟨i.val - 192, by omega⟩
  by_cases h4 : i.val < 320
  · simpa only [scheduledChunk, show 256 + (i.val - 256) = i.val by omega] using
      distinct4 ⟨i.val - 256, by omega⟩
  by_cases h5 : i.val < 384
  · simpa only [scheduledChunk, show 320 + (i.val - 320) = i.val by omega] using
      distinct5 ⟨i.val - 320, by omega⟩
  by_cases h6 : i.val < 448
  · simpa only [scheduledChunk, show 384 + (i.val - 384) = i.val by omega] using
      distinct6 ⟨i.val - 384, by omega⟩
  by_cases h7 : i.val < 512
  · simpa only [scheduledChunk, show 448 + (i.val - 448) = i.val by omega] using
      distinct7 ⟨i.val - 448, by omega⟩
  by_cases h8 : i.val < 576
  · simpa only [scheduledChunk, show 512 + (i.val - 512) = i.val by omega] using
      distinct8 ⟨i.val - 512, by omega⟩
  by_cases h9 : i.val < 640
  · simpa only [scheduledChunk, show 576 + (i.val - 576) = i.val by omega] using
      distinct9 ⟨i.val - 576, by omega⟩
  · simpa only [scheduledChunk, show 640 + (i.val - 640) = i.val by omega] using
      distinct10 ⟨i.val - 640, by omega⟩

end Airbender.Keccak.Proofs
