import Airbender.Review.Circuits.ReducedMachine.WorkerSignedClocks
import Airbender.Proofs.ReducedMachine.NativeDelegationSupport
import Airbender.Proofs.ReducedMachine.NativeWorkerClockProgress

namespace Airbender.NativeWorkerSignedClockProofs
open Airbender.NativeWorkerSignedClocks Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic modular interval reasoning BEFORE M31/native data instantiation. -/
private theorem cast_interval (p : Nat) (x y : Int)
    (lower : -(p : Int) < x-y) (upper : x-y < (p : Int))
    (equal : (x : ZMod p) = (y : ZMod p)) : x = y := by
  have zero : ((x-y : Int) : ZMod p) = 0 := by rw [Int.cast_sub,equal,sub_self]
  have remainder := (ZMod.intCast_eq_intCast_iff' (x-y) 0 p).mp (by simpa only [Int.cast_zero] using zero)
  simp only [Int.zero_emod] at remainder
  by_cases nonnegative : 0 ≤ x-y
  · rw [Int.emod_eq_of_lt nonnegative upper] at remainder
    omega
  · have positive : 0 ≤ x-y+(p : Int) := by omega
    have small : x-y+(p : Int) < p := by omega
    have shifted : (x-y+(p : Int)) % p = 0 := by
      simpa only [Int.add_emod,Int.emod_self,add_zero,Int.emod_emod] using remainder
    rw [Int.emod_eq_of_lt positive small] at shifted
    omega

private theorem ordered_differences (p base : Nat) (positive : 0 < base) (room : 6*base < p)
    (oldLow low oldHigh high borrow : Int)
    (oldLowBounds : -1 ≤ oldLow ∧ oldLow < 2*(base : Int)-1)
    (lowBounds : -1 ≤ low ∧ low < 2*(base : Int)-1)
    (oldHighBounds : -1 ≤ oldHigh ∧ oldHigh < (base : Int))
    (highBounds : -1 ≤ high ∧ high < (base : Int))
    (boolean : borrow = 0 ∨ borrow = 1)
    (lower : (((oldLow-low+(base : Int)*borrow : Int) : ZMod p)).val < base)
    (upper : ((((base : Int)+oldHigh-high-borrow : Int) : ZMod p)).val < base) :
    oldLow+(base : Int)*oldHigh < low+(base : Int)*high := by
  haveI : NeZero p := ⟨by omega⟩
  let a := oldLow-low+(base : Int)*borrow
  let b := (base : Int)+oldHigh-high-borrow
  have aBound : 0 ≤ (((a : ZMod p).val : Nat) : Int) ∧ ((a : ZMod p).val : Int) < base :=
    ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr lower⟩
  have bBound : 0 ≤ (((b : ZMod p).val : Nat) : Int) ∧ ((b : ZMod p).val : Int) < base :=
    ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr upper⟩
  have aEqual : a = ((a : ZMod p).val : Int) := by
    apply cast_interval p
    · rcases boolean with rfl | rfl <;> dsimp [a] <;> omega
    · rcases boolean with rfl | rfl <;> dsimp [a] <;> omega
    · simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  have bEqual : b = ((b : ZMod p).val : Int) := by
    apply cast_interval p
    · rcases boolean with rfl | rfl <;> dsimp [b] <;> omega
    · rcases boolean with rfl | rfl <;> dsimp [b] <;> omega
    · simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  rw [← aEqual] at aBound
  rw [← bEqual] at bBound
  dsimp [a,b] at aBound bBound
  have basePositive : (0 : Int) < base := Int.ofNat_lt.mpr positive
  nlinarith

theorem sentinel (raw : F) : raw = -1 ↔ raw.val = mersenne31Modulus-1 := by
  constructor
  · intro same
    rw [same]
    decide +kernel
  · intro same
    apply ZMod.val_injective mersenne31Modulus
    rw [same]
    decide +kernel

theorem limb_cast (raw : F) : (limb raw : F) = raw := by
  by_cases negative : raw = -1
  · simp [limb,negative]
  · simp only [limb,if_neg negative,Int.cast_natCast,ZMod.natCast_zmod_val]

private theorem limb_bounds (raw : F) (cutoff : Nat)
    (domain : raw.val < cutoff ∨ raw.val = mersenne31Modulus-1) :
    -1 ≤ limb raw ∧ limb raw < (cutoff : Int) := by
  by_cases negative : raw = -1
  · simp only [limb,if_pos negative]
    omega
  · have small : raw.val < cutoff := domain.resolve_right (fun same => negative ((sentinel raw).mpr same))
    simp only [limb,if_neg negative]
    exact ⟨by omega,Int.ofNat_lt.mpr small⟩

theorem domain_bounds {raw : F × F}
    (domain : Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair raw)) :
    (-1 ≤ limb raw.1 ∧ limb raw.1 < 1048575) ∧ (-1 ≤ limb raw.2 ∧ limb raw.2 < 524288) :=
  ⟨limb_bounds raw.1 1048575 domain.low,
    limb_bounds raw.2 524288 domain.high⟩

theorem domain_lower {raw : F × F}
    (domain : Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair raw)) : -1 ≤ value raw := by
  have bounds := domain_bounds domain
  by_cases negative : raw.2 = -1
  · have highSentinel := (sentinel raw.2).mp negative
    have restricted := domain.highWrap highSentinel
    have small : raw.1 ≠ -1 := by
      intro same
      have lowSentinel := (sentinel raw.1).mp same
      change 524287 ≤ raw.1.val ∧ raw.1.val < 1048575 at restricted
      change raw.1.val = 2147483646 at lowSentinel
      omega
    simp only [value,limb,if_neg small,if_pos negative]
    change 524287 ≤ raw.1.val ∧ raw.1.val < 1048575 at restricted
    omega
  · simp only [value,limb,if_neg negative]
    have nonnegative : (0 : Int) ≤ raw.2.val := Int.natCast_nonneg _
    omega

theorem bounded_nonnegative {raw : F × F} (bounded : (Trace.timeOfPair raw).Bounded) : 0 ≤ value raw := by
  change raw.1.val < 524288 ∧ raw.2.val < 524288 at bounded
  have noLow : raw.1 ≠ -1 := by
    intro same
    have tooLarge := (sentinel raw.1).mp same
    change raw.1.val = 2147483646 at tooLarge
    omega
  have noHigh : raw.2 ≠ -1 := by
    intro same
    have tooLarge := (sentinel raw.2).mp same
    change raw.2.val = 2147483646 at tooLarge
    omega
  simp only [value,limb,if_neg noLow,if_neg noHigh]
  omega

/-- Only complete native BODY plus DERIVED domains; no canonical old-read bound. -/
theorem local_progress {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (active : w constraintsABI.multiplicity = 1)
    (current : Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair (Airbender.NativeActiveWorkerClocks.workerClock w)))
    (slot : Fin 43)
    (previous : Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair (Airbender.NativeWorkerClockProgress.readToken w slot).time)) :
    readValue w slot < workerValue w := by
  have effects := Airbender.Blake2Worker.MemoryProofs.local_effects holds
  let rawOld := (Airbender.NativeWorkerClockProgress.readToken w slot).time
  let rawCurrent := Airbender.NativeActiveWorkerClocks.workerClock w
  have oldBounds := domain_bounds previous
  have currentBounds := domain_bounds current
  let borrow : Int := if w (clockBorrowColumn slot) = 0 then 0 else 1
  have bit := effects.borrowBits slot
  have boolean : borrow = 0 ∨ borrow = 1 := by
    rcases bit with zero | one
    · exact Or.inl (by simp [borrow,zero])
    · exact Or.inr (by simp [borrow,one])
  have castBorrow : (borrow : F) = w (clockBorrowColumn slot) := by
    rcases bit with zero | one
    · simp [borrow,zero]
    · simp [borrow,one]
  have shape := Airbender.NativeWorkerClockProgressProofs.read_time w slot
  have low : (((limb rawOld.1-limb rawCurrent.1+524288*borrow : Int) : F)).val < 524288 := by
    simpa only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,limb_cast,castBorrow,
      rawOld,rawCurrent,shape,Airbender.NativeActiveWorkerClocks.workerClock,lowClockDifference] using effects.lowDifferences slot
  have high : ((((524288 : Int)+limb rawOld.2-limb rawCurrent.2-borrow : Int) : F)).val < 524288 := by
    simpa only [Int.cast_add,Int.cast_sub,Int.cast_ofNat,Nat.cast_ofNat,limb_cast,castBorrow,rawOld,rawCurrent,
      shape,Airbender.NativeActiveWorkerClocks.workerClock,highClockDifference,active,mul_one] using effects.highDifferences slot
  exact ordered_differences mersenne31Modulus 524288 (by decide +kernel) (by decide +kernel)
    (limb rawOld.1) (limb rawCurrent.1) (limb rawOld.2) (limb rawCurrent.2) borrow
    oldBounds.1 currentBounds.1 oldBounds.2 currentBounds.2 boolean low high

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch := by
  have sources := Airbender.NativeActiveWorkerClockProofs.read_clocks embed memory ch pc gamma config accepted
  have domains := Airbender.NativeDelegationSupportProofs.clock_domain embed memory ch pc gamma config accepted identity
  have readDomains := Airbender.NativeDelegationSupportProofs.read_domains embed memory ch pc gamma config accepted identity
  have progress : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch,
      w constraintsABI.multiplicity = 1 → ∀ slot : Fin 43, readValue w slot < workerValue w := by
    intro w member active slot
    exact local_progress (sources.processing w member).body active (domains w member active) slot
      (readDomains _ (Airbender.NativeWorkerClockProgressProofs.read_member proofs member slot))
  have nonnegative : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch,
      w constraintsABI.multiplicity = 1 → 0 ≤ workerValue w := by
    intro w member active
    have lower := domain_lower (readDomains _ (Airbender.NativeWorkerClockProgressProofs.read_member proofs member (0 : Fin 43)))
    have less := progress w member active (0 : Fin 43)
    change -1 ≤ readValue w (0 : Fin 43) at lower
    omega
  have reads : ∀ token ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false, 0 ≤ value token.time := by
    intro token member
    rcases sources.clocks token member with bounded | writer
    · exact bounded_nonnegative bounded
    · obtain ⟨w,source,_,active,_,same⟩ := writer
      rw [same]
      exact nonnegative w source active
  have positive : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch,
      w constraintsABI.multiplicity = 1 → 0 < workerValue w := by
    intro w member active
    have lower := reads _ (Airbender.NativeWorkerClockProgressProofs.read_member proofs member (0 : Fin 43))
    have less := progress w member active (0 : Fin 43)
    change 0 ≤ readValue w (0 : Fin 43) at lower
    omega
  refine ⟨reads,positive,progress,?_⟩
  intro w member active zero
  have greater := positive w member active
  have equal : workerValue w = 0 := by simp [workerValue,zero,value,limb]
  omega
theorem dependency_order {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (result : Effects proofs batch) {writer reader : Nat → F} (edge : Dependency batch writer reader) :
    workerValue writer < workerValue reader := by
  obtain ⟨_,member,_,active,writeSlot,readSlot,same⟩ := edge
  have clock := congrArg Trace.MemoryToken.time same
  rw [Airbender.NativeActiveWorkerClockProofs.write_clock] at clock
  have order := result.progress reader member active readSlot
  change value (Airbender.NativeWorkerClockProgress.readToken reader readSlot).time < workerValue reader at order
  rw [← clock] at order
  exact order

theorem no_cycles {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (result : Effects proofs batch) : NoWorkerCycles batch := by
  have transitive : ∀ {a b}, Relation.TransGen (Dependency batch) a b → workerValue a < workerValue b := by
    intro a b path
    induction path with
    | single edge => exact dependency_order result edge
    | tail _ edge ih => exact lt_trans ih (dependency_order result edge)
  intro w cycle
  exact (lt_irrefl (workerValue w)) (transitive cycle)

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers ∧ NoWorkerCycles workers := by
  have result := effects embed memory ch pc gamma config accepted.component identity
  exact ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,result,no_cycles result⟩
end Airbender.NativeWorkerSignedClockProofs
