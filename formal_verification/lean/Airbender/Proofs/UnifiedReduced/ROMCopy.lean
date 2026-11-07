import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.ROMValue
import Airbender.Proofs.UnifiedReduced.ROMRow

namespace Airbender.UnifiedReduced.ROMView
open Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

private theorem public_word {before : Reference.RiscV.Sail.State} {lo hi : Nat}
    (low : lo < 65536) (high : hi < 64) (aligned : (lo + 65536 * hi) % 4 = 0) :
    (Trace.ROMView.publicWord before (Nat.pair 1 (Nat.pair lo hi))).toBitVec =
      ROM.words before ((lo + 65536 * hi) / 4) := by
  have bound : (Word.mk lo hi).Bounded := ⟨low, by change hi < 65536; omega⟩
  have address := Word.toBitVec_toNat bound
  change (Word.mk lo hi).toBitVec.toNat = lo + 65536 * hi at address
  have multiple : 4 * ((lo + 65536 * hi) / 4) = lo + 65536 * hi := by omega
  simp only [Trace.ROMView.publicWord, Nat.unpair_pair, Cell.read, ROM.words, address, multiple]
  cases result : (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4
      (lo + 65536 * hi)).run before with
  | ok value state => exact Word.ofBitVec_roundtrip value
  | error error state => rfl

theorem row_word_copy [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p} (store : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (active : w 4 = 1) (load : w 28 = if store then 0 else 1)
    (storeFlag : w 29 = if store then 1 else 0) :
    let interpreted := (row before (⟨.machine, w⟩ : Row p UnifiedFamily)).assignment
    (Word.mk (interpreted 50).val (interpreted 51).val).toBitVec =
      (Word.mk (interpreted 42).val (interpreted 43).val).toBitVec := by
  cases store
  · by_cases rom : w 54 = 1
    · have value := Proofs.word_rom_value hp holds active load rom
      have lowBound := Verification.range16_bound (Verification.lookup_of_holds holds ⟨6, by rw [lookup_count]; decide⟩)
      have lowBound : (w 38).val < 65536 := by
        simpa [Expression.eval, Verification.environment, limbBase] using lowBound
      have physical := public_word (before := before) lowBound value.1 value.2.1
      have ranges := Trace.ROMView.public_word_bound before (Nat.pair 1 (Nat.pair (w 38).val (w 39).val))
      have low : (Trace.ROMView.publicWord before (Nat.pair 1 (Nat.pair (w 38).val (w 39).val))).lo < p := by
        exact lt_of_lt_of_le ranges.1 (by change 65536 ≤ p; omega)
      have high : (Trace.ROMView.publicWord before (Nat.pair 1 (Nat.pair (w 38).val (w 39).val))).hi < p := by
        exact lt_of_lt_of_le ranges.2 (by change 65536 ≤ p; omega)
      simp only [row, load, rom, Bool.false_eq_true, if_false, and_self, if_true, readData,
        show (43 = 42) = False by decide,
        ZMod.val_natCast_of_lt low, ZMod.val_natCast_of_lt high]
      exact value.2.2.trans physical.symm
    · have flag : w 54 = 0 := by
        rcases Proofs.local_flags holds 22 with zero | one
        · exact zero
        · exact False.elim (rom one)
      have copied := Proofs.word_memory_copy false holds load storeFlag flag
      simp [row, load, flag, copied.1, copied.2]
  · have readonly := Verification.assertion_of_holds holds ⟨38, by rw [constraint_count]; decide⟩
    have flag : w 54 = 0 := by
      simpa [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
        storeFlag] using readonly
    have copied := Proofs.word_memory_copy true holds load storeFlag flag
    simp [row, load, copied.1, copied.2]

end Airbender.UnifiedReduced.ROMView
