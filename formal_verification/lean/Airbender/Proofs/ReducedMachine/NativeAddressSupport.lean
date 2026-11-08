import Airbender.Review.Circuits.ReducedMachine.AddressSupport
import Airbender.Proofs.ReducedMachine.NativeMemoryRoots

namespace Airbender.NativeAddressSupportProofs
open Airbender.NativeAddressSupport
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Entire generic invariant calculation before native rows or seed domains. -/
theorem path_invariant {A B : Type} (relation : A → A → Prop) (observe : A → B)
    (preserves : ∀ a b, relation a b → observe a = observe b)
    {a b : A} (path : Relation.ReflTransGen relation a b) : observe a = observe b := by
  induction path with
  | refl => rfl
  | tail _ edge ih => exact ih.trans (preserves _ _ edge)

/-- Seed-cell arithmetic before actual observed seed lists. -/
theorem cell_address (cell : Trace.Cell) :
    Airbender.NativeMemoryTokens.encodeAddress (cellAddress cell) = cell.addressCode ∧ Domain (cellAddress cell) := by
  have room : 65536 < mersenne31Modulus := by decide +kernel
  cases cell with
  | register index =>
    have small : index.toNat < 32 := index.isLt
    have field : index.toNat < mersenne31Modulus := by omega
    have canonical : ((index.toNat : Nat) : F).val = index.toNat := ZMod.val_natCast_of_lt field
    constructor
    · simp [cellAddress,Airbender.NativeMemoryTokens.encodeAddress,Trace.Cell.addressCode,canonical]
    · left
      exact ⟨rfl,by simpa only [cellAddress,canonical] using small,rfl⟩
  | ram address =>
    have one : (1 : F).val = 1 := by decide +kernel
    have bounds := Arithmetic.Word.ofBitVec_bound address
    have low : (Arithmetic.Word.ofBitVec address).lo < 65536 := bounds.1
    have high : (Arithmetic.Word.ofBitVec address).hi < 65536 := bounds.2
    have loCast : (((Arithmetic.Word.ofBitVec address).lo : Nat) : F).val = (Arithmetic.Word.ofBitVec address).lo :=
      ZMod.val_natCast_of_lt (lt_trans low room)
    have hiCast : (((Arithmetic.Word.ofBitVec address).hi : Nat) : F).val = (Arithmetic.Word.ofBitVec address).hi :=
      ZMod.val_natCast_of_lt (lt_trans high room)
    constructor
    · simp [cellAddress,Airbender.NativeMemoryTokens.encodeAddress,Trace.Cell.addressCode,loCast,hiCast,one]
    · right
      exact ⟨rfl,by simpa only [cellAddress,loCast] using low,by simpa only [cellAddress,hiCast] using high⟩

theorem domain_of_code {address : MemoryKeyAddress} {cell : Trace.Cell}
    (same : Airbender.NativeMemoryTokens.encodeAddress address = cell.addressCode) : Domain address := by
  have bound := cell_address cell
  have raw : address = cellAddress cell := Airbender.NativeMemoryTokenProofs.address_injective (same.trans bound.1.symm)
  exact raw ▸ bound.2

/-- Every actual memory edge preserves its raw address. No expected read,
    source key, word bound or worker result is supplied. -/
theorem step_address {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {read write : Token} (step : Airbender.NativeMixedMemoryOrder.Step proofs batch read write) :
    read.address = write.address := by
  rcases step with ⟨row,_,port,_,rfl,rfl⟩ | ⟨w,_,_,slot,rfl,rfl⟩ <;> rfl

theorem main_address (w : Nat → F) (port : Trace.MemoryPort) (actual : port ∈ importedConstraintsMemoryPorts) :
    Airbender.NativeMemoryTokens.encodeAddress (Airbender.ReducedMachine.NativeMainAuxiliary.nativeAddress w port.address) =
      (Trace.readToken w port).address := by
  have member : port ∈ (List.finRange 3).map Airbender.ReducedMachine.NativeMainAuxiliary.mainPort := by
    rw [Airbender.NativeMemoryTokenProofs.port_order]
    simpa using actual
  obtain ⟨slot,_,rfl⟩ := List.mem_map.mp member
  exact congrArg Trace.MemoryToken.address (Airbender.NativeMemoryTokenProofs.main_token w slot false)

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch inputs := by
  have roots := Airbender.NativeMemoryRootsProofs.effects embed memory ch pc gamma config accepted identity
  have seeds := Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted
  have cells : ∀ read write, Airbender.NativeMixedMemoryOrder.Step proofs batch read write →
      ∃ cell ∈ Airbender.NativeInitializationSeedBoundary.cells proofs,
        read.address = cell.addressCode ∧ write.address = cell.addressCode := by
    intro read write step
    obtain ⟨seed,member,path⟩ := roots.reads read write step
    have same := path_invariant _ Trace.MemoryToken.address (fun _ _ edge => step_address edge) path
    rw [seeds.encoding] at member
    obtain ⟨cell,present,encoded⟩ := List.mem_map.mp member
    have code : seed.address = cell.addressCode := by rw [← encoded]; rfl
    exact ⟨cell,present,same.symm.trans code,(step_address step).symm.trans (same.symm.trans code)⟩
  refine ⟨roots,cells,?_,?_⟩
  · intro row member port actual
    obtain ⟨cell,_,read,_⟩ := cells _ _ (Or.inl ⟨row,member,port,actual,rfl,rfl⟩)
    cases row with
    | mk family w =>
      cases family
      exact domain_of_code ((main_address w port actual).trans read)
  · intro w member active slot
    obtain ⟨cell,_,read,_⟩ := cells _ _ (Or.inr ⟨w,member,active,slot,rfl,rfl⟩)
    exact domain_of_code read

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩
end Airbender.NativeAddressSupportProofs
