import Airbender.Review.Circuits.ReducedMachine.MixedMemoryOrder
import Airbender.Proofs.ReducedMachine.NativeWorkerSignedClocks
import Airbender.Proofs.ReducedMachine.NativeMemoryHistory

namespace Airbender.NativeMixedMemoryOrderProofs
open Airbender.NativeMixedMemoryOrder
open Airbender.NativeWorkerSignedClocks (value limb)
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Verification
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

/-- Reuse the original complete-BODY query extraction WITHOUT ClockInputs.previous.
    The table stays abstract before any native runtime-pool instantiation. -/
theorem main_queries {p : Nat} [Fact p.Prime] {w : Nat → ZMod p} {setup : Table (ZMod p) (fields 4)}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    ∀ port ∈ importedConstraintsTraceColumns.ports,
      w port.borrow * (w port.borrow-1) = 0 ∧
      ((w port.previous[0]-w 2-port.offset+524288*w port.borrow) : ZMod p).val < 524288 ∧
      ((w port.previous[1]+524288-w port.borrow-w 3) : ZMod p).val < 524288 := by
  intro port member
  simp [importedConstraintsTraceColumns] at member
  rcases member with rfl | rfl | rfl
  · simp only [Nat.cast_zero]
    change w 134 * (w 134 - 1) = 0 ∧
      ((w 132 - w 2 - 0 + 524288 * w 134) : ZMod p).val < 524288 ∧
      ((w 133 + 524288 - w 134 - w 3) : ZMod p).val < 524288
    have bit := Verification.assertion_of_holds h ⟨27, by change 27 < 117; decide⟩
    have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
      ⟨10, by change 10 < 22; decide⟩)
    have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
      ⟨11, by change 11 < 22; decide⟩)
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit
    simp [Expression.eval, Verification.environment] at lower upper
    refine ⟨?_, ?_, ?_⟩
    · convert bit using 1; ring
    · convert lower using 1; congr 1; ring
    · convert upper using 1; congr 1; ring
  · simp only [Nat.cast_one]
    change w 137 * (w 137 - 1) = 0 ∧
      ((w 135 - w 2 - 1 + 524288 * w 137) : ZMod p).val < 524288 ∧
      ((w 136 + 524288 - w 137 - w 3) : ZMod p).val < 524288
    have bit := Verification.assertion_of_holds h ⟨28, by change 28 < 117; decide⟩
    have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
      ⟨12, by change 12 < 22; decide⟩)
    have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
      ⟨13, by change 13 < 22; decide⟩)
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit
    simp [Expression.eval, Verification.environment] at lower upper
    refine ⟨?_, ?_, ?_⟩
    · convert bit using 1; ring
    · convert lower using 1; congr 1; ring
    · convert upper using 1; congr 1; ring
  · simp only [Nat.cast_ofNat]
    change w 140 * (w 140 - 1) = 0 ∧
      ((w 138 - w 2 - 2 + 524288 * w 140) : ZMod p).val < 524288 ∧
      ((w 139 + 524288 - w 140 - w 3) : ZMod p).val < 524288
    have bit := Verification.assertion_of_holds h ⟨29, by change 29 < 117; decide⟩
    have lower := Verification.timestamp19_bound (Verification.lookup_of_holds h
      ⟨14, by change 14 < 22; decide⟩)
    have upper := Verification.timestamp19_bound (Verification.lookup_of_holds h
      ⟨15, by change 15 < 22; decide⟩)
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit
    simp [Expression.eval, Verification.environment] at lower upper
    refine ⟨?_, ?_, ?_⟩
    · convert bit using 1; ring
    · convert lower using 1; congr 1; ring
    · convert upper using 1; congr 1; ring

private theorem bounded_domain (clock : Trace.Timestamp) (bounded : clock.Bounded) :
    Airbender.NativeCallerClockDomain.Domain clock := by
  change clock.lo < 524288 ∧ clock.hi < 524288 at bounded
  refine ⟨Or.inl (by have lower := bounded.1; omega),Or.inl bounded.2,fun _ => bounded.2,?_⟩
  intro sentinel
  have upper := bounded.2
  change clock.hi = 2147483646 at sentinel
  omega

/-- Full BODY, derived actual WRITE bound, and separately derived old-read domain.
    There is no old-read19bit or expected-clock premise. -/
theorem main_port_progress {w : Nat → F} {setup : Table F (fields 4)}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (port : Trace.MemoryPort) (member : port ∈ importedConstraintsMemoryPorts)
    (writeBound : (Trace.timeOfPair (Trace.writeToken importedConstraintsTraceColumns w port).time).Bounded)
    (readDomain : Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair (Trace.readToken w port).time)) :
    value (Trace.readToken w port).time < value (Trace.writeToken importedConstraintsTraceColumns w port).time := by
  have mapped : port.clock ∈ importedConstraintsMemoryPorts.map Trace.MemoryPort.clock :=
    Array.mem_map.mpr ⟨port,member,rfl⟩
  rw [Airbender.ReducedMachine.NativeClockProofs.memory_clocks] at mapped
  have q := main_queries holds port.clock mapped
  have bit : w port.clock.borrow = 0 ∨ w port.clock.borrow = 1 :=
    (mul_eq_zero.mp q.1).imp_right sub_eq_zero.mp
  let rawOld := (Trace.readToken w port).time
  let rawCurrent := (Trace.writeToken importedConstraintsTraceColumns w port).time
  let borrow : Int := if w port.clock.borrow = 0 then 0 else 1
  have boolean : borrow = 0 ∨ borrow = 1 := by
    rcases bit with zero | one
    · exact Or.inl (by simp [borrow,zero])
    · exact Or.inr (by simp [borrow,one])
  have castBorrow : (borrow : F) = w port.clock.borrow := by
    rcases bit with zero | one
    · simp [borrow,zero]
    · simp [borrow,one]
  have oldBounds := Airbender.NativeWorkerSignedClockProofs.domain_bounds readDomain
  have currentBounds := Airbender.NativeWorkerSignedClockProofs.domain_bounds (bounded_domain _ writeBound)
  have oldLow : rawOld.1 = w port.clock.previous[0] := rfl
  have oldHigh : rawOld.2 = w port.clock.previous[1] := rfl
  have currentLow : rawCurrent.1 = w 2+port.clock.offset := rfl
  have currentHigh : rawCurrent.2 = w 3 := rfl
  have lowEquality : (((limb rawOld.1-limb rawCurrent.1+524288*borrow : Int) : F)) =
      w port.clock.previous[0]-w 2-port.clock.offset+524288*w port.clock.borrow := by
    simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,
      Airbender.NativeWorkerSignedClockProofs.limb_cast,castBorrow,oldLow,currentLow]
    ring
  have highEquality : ((((524288 : Int)+limb rawOld.2-limb rawCurrent.2-borrow : Int) : F)) =
      w port.clock.previous[1]+524288-w port.clock.borrow-w 3 := by
    simp only [Int.cast_add,Int.cast_sub,Int.cast_ofNat,
      Airbender.NativeWorkerSignedClockProofs.limb_cast,castBorrow,oldHigh,currentHigh]
    ring
  have low : (((limb rawOld.1-limb rawCurrent.1+524288*borrow : Int) : F)).val < 524288 := by
    rw [lowEquality]
    exact q.2.1
  have high : ((((524288 : Int)+limb rawOld.2-limb rawCurrent.2-borrow : Int) : F)).val < 524288 := by
    rw [highEquality]
    exact q.2.2
  exact ordered_differences mersenne31Modulus 524288 (by decide +kernel) (by decide +kernel)
    (limb rawOld.1) (limb rawCurrent.1) (limb rawOld.2) (limb rawCurrent.2) borrow
    oldBounds.1 currentBounds.1 oldBounds.2 currentBounds.2 boolean low high

theorem main_read_member {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    {row : MainRow} (member : row ∈ mainRows proofs) {port : Trace.MemoryPort} (actual : port ∈ row.ports) :
    Trace.readToken row.assignment port ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false := by
  have source : Trace.readToken row.assignment port ∈ (mainRows proofs).flatMap Trace.Row.reads :=
    List.mem_flatMap.mpr ⟨row,member,List.mem_map.mpr ⟨port,by simpa using actual,rfl⟩⟩
  have projection := Airbender.NativeMemoryHistoryProofs.main_projection proofs false
  change (mainRows proofs).flatMap Trace.Row.reads = _ at projection
  rw [projection] at source
  exact List.mem_append_left _ source

theorem step_read_member {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {read write : Token} (edge : Step proofs batch read write) :
    read ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false := by
  rcases edge with ⟨row,member,port,actual,rfl,_⟩ | ⟨w,member,_,slot,rfl,_⟩
  · exact main_read_member proofs batch member actual
  · exact Airbender.NativeWorkerClockProgressProofs.read_member proofs member slot

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch := by
  have workerResult := Airbender.NativeWorkerSignedClockProofs.effects embed memory ch pc gamma config accepted identity
  have components := Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted
  have state := Airbender.NativeMainStateHistoryProofs.history embed memory pc components accepted.matching
  have body := Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ components
  have readDomains := Airbender.NativeDelegationSupportProofs.read_domains embed memory ch pc gamma config accepted identity
  have mains : ∀ row ∈ mainRows proofs, ∀ port ∈ row.ports,
      value (Trace.readToken row.assignment port).time < value (Trace.writeToken row.columns row.assignment port).time := by
    intro row member port actual
    have holds := body row member
    have bounded := (state.writes row member port actual).1
    have domain := readDomains _ (main_read_member proofs batch member actual)
    cases row with
    | mk family w =>
      cases family
      exact main_port_progress holds port actual bounded domain
  have steps : ∀ read write, Step proofs batch read write → value read.time < value write.time := by
    intro read write edge
    rcases edge with ⟨row,member,port,actual,rfl,rfl⟩ | ⟨w,member,active,slot,rfl,rfl⟩
    · exact mains row member port actual
    · rw [Airbender.NativeActiveWorkerClockProofs.write_clock]
      exact workerResult.progress w member active slot
  have transitive : ∀ {a b}, Relation.TransGen (Step proofs batch) a b → value a.time < value b.time := by
    intro a b path
    induction path with
    | single edge => exact steps _ _ edge
    | tail _ edge ih => exact lt_trans ih (steps _ _ edge)
  exact ⟨workerResult,mains,steps,fun token cycle => (lt_irrefl (value token.time)) (transitive cycle)⟩

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩
end Airbender.NativeMixedMemoryOrderProofs
