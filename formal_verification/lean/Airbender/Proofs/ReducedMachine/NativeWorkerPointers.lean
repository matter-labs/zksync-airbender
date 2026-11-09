import Airbender.Proofs.ReducedMachine.NativeMemoryWriteUniqueness
import Airbender.Review.Trace.Families.ReducedMachine.WorkerPointers

namespace Airbender.NativeWorkerPointersProofs
open Airbender.NativeWorkerPointers
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine.Native Airbender.NativeWorkerSnapshot
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Locate the last value-changing edge on an actual finite path, BEFORE native
    tokens or domains. The exact final value and residual path are conclusions. -/
theorem last_change {A V : Type} [Zero V] (relation : A → A → Prop) (value : A → V)
    {a b : A} (path : Relation.ReflTransGen relation a b) (zero : value a = 0) (nonzero : value b ≠ 0) :
    ∃ prior fresh, relation prior fresh ∧ value fresh = value b ∧ value fresh ≠ value prior ∧
      Relation.ReflTransGen relation fresh b := by
  induction path with
  | refl => exact (nonzero zero).elim
  | @tail b c path edge ih =>
    by_cases same : value c = value b
    · obtain ⟨prior,fresh,actual,final,changed,suffix⟩ := ih (by simpa only [← same] using nonzero)
      exact ⟨prior,fresh,actual,final.trans same.symm,changed,suffix.tail edge⟩
    · exact ⟨b,c,edge,rfl,same,Relation.ReflTransGen.refl⟩

theorem geometry :
    (keyDescriptor (0 : Fin 43)).location = .register 10 ∧
    (keyDescriptor (25 : Fin 43)).location = .register 11 ∧
    (keyDescriptor (42 : Fin 43)).location = .register 12 ∧
    (keyDescriptor (1 : Fin 43)).location = .indirect #v[2,3] 0 ∧
    (keyDescriptor (26 : Fin 43)).location = .indirect #v[100,101] 0 ∧
    (memoryAccess (0 : Fin 43)).readValue = #v[2,3] ∧
    (memoryAccess (25 : Fin 43)).readValue = #v[100,101] ∧
    (memoryAccess (0 : Fin 43)).writeValue = none ∧
    (memoryAccess (25 : Fin 43)).writeValue = none := by decide +kernel

def direct (slot : Fin 43) : Bool := match (keyDescriptor slot).location with
  | .register _ => true
  | .indirect _ _ => false

theorem direct_slots : ∀ slot : Fin 43, direct slot = true ↔ slot = 0 ∨ slot = 25 ∨ slot = 42 := by decide +kernel

theorem pointer_codes (w : Nat → F) :
    (read w 0).address = Nat.pair 0 (Nat.pair 10 0) ∧
    (read w 25).address = Nat.pair 0 (Nat.pair 11 0) ∧
    (read w 42).address = Nat.pair 0 (Nat.pair 12 0) ∧
    (write w 1).address = Nat.pair 1 (read w 0).value ∧
    (write w 26).address = Nat.pair 1 (read w 25).value := by
  rcases geometry with ⟨d0,d25,d42,d1,d26,v0,v25,_,_⟩
  have one : (1 : F).val = 1 := by decide +kernel
  simp [Airbender.NativeWorkerSnapshot.read,Airbender.NativeWorkerSnapshot.write,Airbender.NativeWorkerClockProgress.readToken,
    Airbender.NativeMemoryTokens.encodeKey,Airbender.NativeMemoryTokens.encodeAddress,
    quotientMemoryKey,d0,d25,d42,d1,d26,quotientKeyAddress,keyValue,v0,v25,one]
  decide +kernel

theorem readonly_pointer (w : Nat → F) (pointer : Fin 2) :
    (write w (pointerSlot pointer)).value = (read w (pointerSlot pointer)).value := by
  have r0 := geometry.2.2.2.2.2.2.2.1
  have r25 := geometry.2.2.2.2.2.2.2.2
  fin_cases pointer <;> simp [pointerSlot,Airbender.NativeWorkerSnapshot.read,Airbender.NativeWorkerSnapshot.write,Airbender.NativeWorkerClockProgress.readToken,
    Airbender.NativeMemoryTokens.encodeKey,quotientMemoryKey,keyValue,r0,r25]

theorem ram_space (w : Nat → F) (slot : Fin 43) (indirect : direct slot = false) :
    (Nat.unpair (read w slot).address).1 = 1 := by
  cases h : (keyDescriptor slot).location with
  | register index => simp [direct,h] at indirect
  | indirect base offset =>
    have one : (1 : F).val = 1 := by decide +kernel
    simp [Airbender.NativeWorkerSnapshot.read,Airbender.NativeWorkerClockProgress.readToken,Airbender.NativeMemoryTokens.encodeKey,
      Airbender.NativeMemoryTokens.encodeAddress,quotientMemoryKey,h,quotientKeyAddress,one]

theorem worker_preserves (w : Nat → F) (slot : Fin 43)
    (address : (read w slot).address = Nat.pair 0 (Nat.pair 10 0) ∨
      (read w slot).address = Nat.pair 0 (Nat.pair 11 0)) :
    (write w slot).value = (read w slot).value := by
  cases h : direct slot with
  | false =>
    have ram := ram_space w slot h
    rcases address with same | same <;> rw [same] at ram <;> norm_num at ram
  | true =>
    rcases (direct_slots slot).mp h with rfl | rfl | rfl
    · exact readonly_pointer w 0
    · exact readonly_pointer w 1
    · rw [(pointer_codes w).2.2.1] at address
      norm_num at address

theorem pointer_distinct {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} (unique : Airbender.NativeMemoryWriteUniqueness.Effects proofs workers inputs)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers) (active : w constraintsABI.multiplicity = 1) :
    (read w 0).value ≠ (read w 25).value := by
  intro same
  have aliases : (write w 1).address = (write w 26).address := by
    rw [(pointer_codes w).2.2.2.1,(pointer_codes w).2.2.2.2,same]
  have slots := unique.workerAddresses w member active aliases
  have bad : (1 : Fin 43) ≠ 26 := by decide +kernel
  exact bad slots

theorem changed_main_port (row : Airbender.NativeMixedMemoryOrder.MainRow) (port : Trace.MemoryPort)
    (actual : port ∈ row.ports)
    (changed : (Trace.writeToken row.columns row.assignment port).value ≠ (Trace.readToken row.assignment port).value) :
    port = Airbender.ReducedMachine.NativeMainAuxiliary.mainPort 2 := by
  cases row with
  | mk family w =>
    cases family
    change port ∈ importedConstraintsMemoryPorts at actual
    have member : port ∈ (List.finRange 3).map Airbender.ReducedMachine.NativeMainAuxiliary.mainPort := by
      rw [Airbender.NativeMemoryTokenProofs.port_order]
      simpa using actual
    obtain ⟨slot,_,rfl⟩ := List.mem_map.mp member
    fin_cases slot
    · exact (changed rfl).elim
    · exact (changed rfl).elim
    · rfl

theorem seed_zero {R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    (seeds : Airbender.NativeInitializationSeedBoundary.Effects proofs)
    {token : Airbender.NativeMixedMemoryOrder.Token} (member : token ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs) :
    token.value = 0 := by
  rw [seeds.encoding] at member
  obtain ⟨cell,_,rfl⟩ := List.mem_map.mp member
  rfl

theorem main_active {R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {row : Airbender.NativeMixedMemoryOrder.MainRow} (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs) :
    row.assignment importedConstraintsTraceColumns.execute = 1 := by
  obtain ⟨w,wm,rfl⟩ := List.mem_map.mp member
  exact of_decide_eq_true (List.mem_filter.mp wm).2

theorem pointer_target (w : Nat → F) (pointer : Fin 2) :
    (read w (pointerSlot pointer)).address = Nat.pair 0 (Nat.pair 10 0) ∨
      (read w (pointerSlot pointer)).address = Nat.pair 0 (Nat.pair 11 0) := by
  fin_cases pointer
  · exact Or.inl (pointer_codes w).1
  · exact Or.inr (pointer_codes w).2.1

/-- Derive an exact value-changing MAIN source from the actual seed path. -/
theorem origin {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} (unique : Airbender.NativeMemoryWriteUniqueness.Effects proofs workers inputs)
    (seeds : Airbender.NativeInitializationSeedBoundary.Effects proofs)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers) (active : w constraintsABI.multiplicity = 1)
    (pointer : Fin 2) (nonzero : (read w (pointerSlot pointer)).value ≠ 0) :
    MainOrigin proofs workers (read w (pointerSlot pointer)) := by
  have roots := unique.paths.keys.addresses.roots
  obtain ⟨seed,present,path⟩ := roots.reads _ _ (Or.inr ⟨w,member,active,pointerSlot pointer,rfl,rfl⟩)
  obtain ⟨prior,fresh,edge,value,changed,suffix⟩ := last_change _ Trace.MemoryToken.value path (seed_zero seeds present) nonzero
  have freshAddress := Airbender.NativeAddressSupportProofs.path_invariant _ Trace.MemoryToken.address
    (fun _ _ actual => Airbender.NativeAddressSupportProofs.step_address actual) suffix
  have priorAddress := (Airbender.NativeAddressSupportProofs.step_address edge).trans freshAddress
  rcases edge with ⟨row,rm,port,pm,rfl,rfl⟩ | ⟨worker,_,_,slot,rfl,rfl⟩
  · exact ⟨row,rm,port,pm,main_active rm,changed_main_port row port pm changed,freshAddress,value,changed,suffix⟩
  · have address := pointer_target w pointer
    have target : (read worker slot).address = Nat.pair 0 (Nat.pair 10 0) ∨
        (read worker slot).address = Nat.pair 0 (Nat.pair 11 0) := by
      rcases address with same | same
      · exact Or.inl (priorAddress.trans same)
      · exact Or.inr (priorAddress.trans same)
    exact (changed (worker_preserves worker slot target)).elim

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers) (active : w constraintsABI.multiplicity = 1) :
    (read w 0).value ≠ (read w 25).value ∧
    (∀ pointer : Fin 2, (read w (pointerSlot pointer)).value ≠ 0 → MainOrigin proofs workers (read w (pointerSlot pointer))) ∧
    ∃ pointer : Fin 2, (read w (pointerSlot pointer)).value ≠ 0 ∧ MainOrigin proofs workers (read w (pointerSlot pointer)) := by
  have unique := Airbender.NativeMemoryWriteUniquenessProofs.effects embed memory ch pc gamma config accepted identity
  have seeds := Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted
  have distinct := pointer_distinct unique member active
  have origins := origin unique seeds member active
  refine ⟨distinct,origins,?_⟩
  by_cases nonzero : (read w 0).value ≠ 0
  · exact ⟨0,nonzero,origins 0 nonzero⟩
  · have other : (read w 25).value ≠ 0 := by intro zero; exact distinct ((not_ne_iff.mp nonzero).trans zero.symm)
    exact ⟨1,other,origins 1 other⟩

end Airbender.NativeWorkerPointersProofs

