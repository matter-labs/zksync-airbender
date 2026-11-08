import Airbender.Review.Circuits.Blake2Worker.Addition
import Airbender.Proofs.ReducedMachine.NativeWorkerFirstG
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.NativeWorkerAdditionProofs
open Airbender.Verification
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem weighted_sum (bits : Fin 10 → Nat) (values : Fin 10 → F)
    (flags : ∀ i, bits i ≤ 1) (bounds : ∀ i, (values i).val < 65536) :
    (∑ i, (bits i : F)*values i).val = ∑ i, bits i*(values i).val ∧
      (∑ i, bits i*(values i).val) < 655360 := by
  have small : ∀ i, bits i*(values i).val ≤ 65535 := by
    intro i
    have := flags i
    have := bounds i
    calc
      _ ≤ 1*(values i).val := Nat.mul_le_mul_right _ (flags i)
      _ ≤ 65535 := by omega
  have total : (∑ i, bits i*(values i).val) < 655360 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => small i)
    norm_num at h
    omega
  have same : (∑ i, (bits i : F)*values i) = ((∑ i, bits i*(values i).val : Nat) : F) := by
    simp
  exact ⟨by rw [same,ZMod.val_natCast_of_lt (total.trans (by decide +kernel))],total⟩

theorem carry_value (x y : F) (xb : x.val ≤ 1) (yb : y.val ≤ 1) :
    (x+2*y).val = x.val+2*y.val ∧ (x+2*y).val ≤ 3 := by
  have small : x.val+2*y.val < mersenne31Modulus := by
    change x.val+2*y.val < 2147483647
    omega
  have same : x+2*y = ((x.val+2*y.val : Nat) : F) := by simp
  rw [same,ZMod.val_natCast_of_lt small]
  omega

theorem pack_value (low high : F) (lb : low.val < 65536) (hb : high.val < 65536) :
    Airbender.NativeWorkerFirstG.pack low high = BitVec.ofNat 32 (low.val+65536*high.val) := by
  apply BitVec.eq_of_toNat_eq
  change ((high.val % 65536) <<< 16) ||| (low.val % 65536) = (low.val+65536*high.val)%4294967296
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show low.val % 65536 < 2^16 by omega)]
  simp [Nat.shiftLeft_eq,Nat.mod_eq_of_lt lb,Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (show low.val+65536*high.val < 4294967296 by omega)]
  omega

theorem limb_sum (a b m incoming c r : F) (ab : a.val < 65536) (bb : b.val < 65536)
    (mb : m.val < 655360) (ib : incoming.val ≤ 3) (cb : c.val ≤ 3) (rb : r.val < 65536)
    (same : a+b+m+ incoming = r+65536*c) :
    a.val+b.val+m.val+ incoming.val = r.val+65536*c.val := by
  apply Airbender.Arithmetic.bounded_nat_eq (F := F) (p := mersenne31Modulus)
  · change _ < 2147483647; omega
  · change _ < 2147483647; omega
  · simpa using same

theorem wide_add (a0 a1 b0 b1 m0 m1 s0 s1 c0 c1 : Nat)
    (low : a0+b0+m0 = s0+65536*c0)
    (high : a1+b1+m1+c0 = s1+65536*c1) :
    BitVec.ofNat 32 (s0+65536*s1) = BitVec.ofNat 32 (a0+65536*a1) +
      BitVec.ofNat 32 (b0+65536*b1) + BitVec.ofNat 32 (m0+65536*m1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.reducePow]
  omega

open Airbender.Blake2Worker.Native Airbender.NativeWorkerSchedule Airbender.NativeWorkerInitial
private theorem encoded_bound (key : MemoryKey) :
    (Airbender.NativeMemoryTokens.encodeKey key).word.Bounded ↔
      Airbender.NativeWorkerWriteSlices.WordBound key.value := by
  simp only [Airbender.Trace.MemoryToken.word,Airbender.NativeMemoryTokens.encodeKey,Nat.unpair_pair,Airbender.Arithmetic.Word.Bounded]
  change (key.value[0].val < 65536 ∧ key.value[1].val < 65536) ↔ ∀ i : Fin 2, key.value[i].val < 65536
  constructor
  · intro bounds i
    fin_cases i
    · exact bounds.1
    · exact bounds.2
  · intro bounds
    exact ⟨bounds 0,bounds 1⟩

private theorem state_shape (word : Fin 8) :
    (memoryAccess ⟨1+word.val,by have := word.isLt; omega⟩).readValue = #v[4+4*word.val,5+4*word.val] := by
  fin_cases word <;> rfl
private theorem extended_shape (word : Fin 16) :
    (memoryAccess ⟨9+word.val,by have := word.isLt; omega⟩).readValue = #v[36+4*word.val,37+4*word.val] := by
  fin_cases word <;> rfl
private theorem message_shape (word : Fin 16) :
    (memoryAccess ⟨26+word.val,by have := word.isLt; omega⟩).readValue = #v[102+2*word.val,103+2*word.val] := by
  fin_cases word <;> rfl

theorem read_bounds {w : Nat → F}
    (reads : ∀ slot : Fin 43, (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot false)).word.Bounded) :
    (∀ word : Fin 8, ∀ limb : Fin 2, (state w word limb).val < 65536) ∧
    (∀ word : Fin 16, ∀ limb : Fin 2, (oldExtended w word limb).val < 65536) ∧
    (∀ word : Fin 16, ∀ limb : Fin 2, (message w word limb).val < 65536) := by
  have values : ∀ slot : Fin 43, ∀ limb : Fin 2, (w ((memoryAccess slot).readValue[limb])).val < 65536 := by
    intro slot limb
    have h := (encoded_bound _).mp (reads slot) limb
    simpa [quotientMemoryKey,keyValue] using h
  constructor
  · intro word limb
    have h := values ⟨1+word.val,by have := word.isLt; omega⟩ limb
    rw [state_shape] at h
    fin_cases limb
    · simpa [state] using h
    · change (w (4+4*word.val+1)).val < 65536
      rw [show 4+4*word.val+1 = 5+4*word.val by omega]
      exact h
  constructor
  · intro word limb
    have h := values ⟨9+word.val,by have := word.isLt; omega⟩ limb
    rw [extended_shape] at h
    fin_cases limb
    · simpa [oldExtended] using h
    · change (w (36+4*word.val+1)).val < 65536
      rw [show 36+4*word.val+1 = 37+4*word.val by omega]
      exact h
  · intro word limb
    have h := values ⟨26+word.val,by have := word.isLt; omega⟩ limb
    rw [message_shape] at h
    fin_cases limb
    · simpa [message] using h
    · change (w (102+2*word.val+1)).val < 65536
      rw [show 102+2*word.val+1 = 103+2*word.val by omega]
      exact h

theorem initial_bounds {w : Nat → F} (effects : Airbender.NativeWorkerInitial.RowEffects w)
    (states : ∀ word : Fin 8, ∀ limb : Fin 2, (state w word limb).val < 65536)
    (extended : ∀ word : Fin 16, ∀ limb : Fin 2, (oldExtended w word limb).val < 65536) :
    ∀ word : Fin 16, ∀ limb : Fin 2, (observed w word limb).val < 65536 := by
  have constant (n : Nat) (limb : Fin 2) : (limbOf n limb).val < 65536 := by
    unfold limbOf
    rw [ZMod.val_natCast_of_lt (show n / 2^(16*limb.val) % 65536 < mersenne31Modulus from
      (Nat.mod_lt _ (by decide +kernel)).trans (by decide +kernel))]
    exact Nat.mod_lt _ (by decide +kernel)
  intro word limb
  rw [effects.initialized]
  unfold initial finalBase
  split
  · exact extended word limb
  split
  · split
    · exact states _ limb
    · exact constant _ limb
  split
  · split
    · exact extended word limb
    · exact constant _ limb
  · exact constant _ limb

theorem input_bounds {w : Nat → F}
    (states : ∀ word : Fin 8, ∀ limb : Fin 2, (state w word limb).val < 65536)
    (messages : ∀ word : Fin 16, ∀ limb : Fin 2, (message w word limb).val < 65536) :
    ∀ word : Fin 16, ∀ limb : Fin 2, (input w word limb).val < 65536 := by
  intro word limb
  unfold input
  split
  · exact messages word limb
  split
  · split
    · exact messages word limb
    · exact states _ limb
  · split
    · exact states _ limb
    · exact messages _ limb

theorem selected_bounds {w : Nat → F} (effects : Airbender.NativeWorkerSchedule.RowEffects w)
    (inputs : ∀ word : Fin 16, ∀ limb : Fin 2, (input w word limb).val < 65536) :
    ∀ word : Fin 16, ∀ limb : Fin 2, (selected w word limb).val < 655360 := by
  intro word limb
  rw [effects.schedule]
  have h := weighted_sum (fun r : Fin 10 => inputBit w ⟨3+r.val,by omega⟩)
    (fun r => input w sigma[r][word] limb) (fun _ => by unfold inputBit; omega)
    (fun _ => inputs _ _)
  change (∑ r : Fin 10, (inputBit w ⟨3+r.val,by omega⟩ : F)* input w sigma[r][word] limb).val < 655360
  rw [h.1]
  exact h.2

theorem carry_bounds {w : Nat → F} (effects : Airbender.NativeWorkerFirstG.RowEffects w) :
    ∀ column : Fin 4, ∀ limb : Fin 2, (Airbender.NativeWorkerFirstG.carry w column limb).val ≤ 3 := by
  intro column limb
  have low := effects.carries column ⟨2*limb.val,by have := limb.isLt; omega⟩
  have high := effects.carries column ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  dsimp [Airbender.NativeWorkerFirstG.carryBit] at low high
  have high' : (w (269+46*column.val+2*limb.val)).val ≤ 1 := by
    rw [show 269+46*column.val+2*limb.val = 268+46*column.val+(2*limb.val+1) by omega]
    exact high
  exact (carry_value _ _ low high').2

theorem addition {w : Nat → F} (effects : Airbender.NativeWorkerFirstG.RowEffects w)
    (initial : ∀ word : Fin 16, ∀ limb : Fin 2, (observed w word limb).val < 65536)
    (selected : ∀ word : Fin 16, ∀ limb : Fin 2, (Airbender.NativeWorkerSchedule.selected w word limb).val < 655360)
    (column : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (Airbender.NativeWorkerFirstG.sumLimb w column 0) (Airbender.NativeWorkerFirstG.sumLimb w column 1) =
      Airbender.NativeWorkerFirstG.pack (observed w ⟨column.val,by have := column.isLt; omega⟩ 0) (observed w ⟨column.val,by have := column.isLt; omega⟩ 1) +
      Airbender.NativeWorkerFirstG.pack (observed w ⟨4+column.val,by have := column.isLt; omega⟩ 0) (observed w ⟨4+column.val,by have := column.isLt; omega⟩ 1) +
      BitVec.ofNat 32 ((Airbender.NativeWorkerSchedule.selected w ⟨2*column.val,by have := column.isLt; omega⟩ 0).val +
        65536*(Airbender.NativeWorkerSchedule.selected w ⟨2*column.val,by have := column.isLt; omega⟩ 1).val) := by
  let a : Fin 16 := ⟨column.val,by have := column.isLt; omega⟩
  let b : Fin 16 := ⟨4+column.val,by have := column.isLt; omega⟩
  let m : Fin 16 := ⟨2*column.val,by have := column.isLt; omega⟩
  have field (limb : Fin 2) :
      observed w a limb + observed w b limb + Airbender.NativeWorkerSchedule.selected w m limb +
        (if limb.val = 0 then 0 else Airbender.NativeWorkerFirstG.carry w column 0) =
      Airbender.NativeWorkerFirstG.sumLimb w column limb + 65536*Airbender.NativeWorkerFirstG.carry w column limb := by
    dsimp [Airbender.NativeWorkerFirstG.sumLimb,a,b,m]
    ring
  have low := limb_sum _ _ _ (0 : F) _ _ (initial a 0) (initial b 0) (selected m 0)
    (by decide +kernel) (carry_bounds effects column 0) (effects.bounds column 0).1 (by simpa using field 0)
  have high := limb_sum _ _ _ _ _ _ (initial a 1) (initial b 1) (selected m 1)
    (carry_bounds effects column 0) (carry_bounds effects column 1) (effects.bounds column 1).1 (by simpa using field 1)
  simp only [ZMod.val_zero,Nat.add_zero] at low
  rw [pack_value _ _ (effects.bounds column 0).1 (effects.bounds column 1).1,
    pack_value _ _ (initial a 0) (initial a 1),pack_value _ _ (initial b 0) (initial b 1)]
  exact wide_add _ _ _ _ _ _ _ _ _ _ low high

theorem selected_values {w : Nat → F} (effects : Airbender.NativeWorkerSchedule.RowEffects w)
    (inputs : ∀ word : Fin 16, ∀ limb : Fin 2, (input w word limb).val < 65536) :
    ∀ word : Fin 16, ∀ limb : Fin 2,
      (selected w word limb).val = Airbender.NativeWorkerAddition.selectedNatural w word limb ∧
        Airbender.NativeWorkerAddition.selectedNatural w word limb < 655360 := by
  intro word limb
  rw [effects.schedule]
  exact weighted_sum (fun r : Fin 10 => inputBit w ⟨3+r.val,by omega⟩)
    (fun r => input w sigma[r][word] limb) (fun _ => by unfold inputBit; omega) (fun _ => inputs _ _)

/-- Internal assembly uses only already-derived initialized raw read bounds. -/
theorem row {w : Nat → F} (prior : Airbender.NativeWorkerFirstG.RowEffects w)
    (reads : ∀ slot : Fin 43, (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot false)).word.Bounded) :
    Airbender.NativeWorkerAddition.RowEffects w := by
  have read := read_bounds reads
  have initial := initial_bounds prior.initial read.1 read.2.1
  have inputs := input_bounds read.1 read.2.2
  have selected := selected_bounds prior.initial.schedule inputs
  exact ⟨prior,initial,inputs,selected_values prior.initial.schedule inputs,carry_bounds prior,
    fun column => addition prior initial selected column⟩
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary
theorem counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeMixedReplay.Effects batch workers inputs ∧
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerAddition.RowEffects w := by
  have prior := Airbender.NativeWorkerFirstGProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  exact ⟨prior.1,fun w member => row (prior.2 w member) (fun slot => prior.1.words.workers w member slot false)⟩
end Airbender.NativeWorkerAdditionProofs
