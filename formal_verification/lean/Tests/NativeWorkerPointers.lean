import Airbender.Review.Trace.Families.ReducedMachine.WorkerPointersTheorems

namespace Airbender.Tests.NativeWorkerPointers
open Airbender.NativeWorkerPointers Airbender.NativeWorkerPointersProofs
open Airbender.NativeWorkerSnapshot Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem two_actual_ports : pointerSlot 0 = 0 ∧ pointerSlot 1 = 25 := by decide +kernel

theorem pointer_gpr_reads (w : Nat → F) :
    (read w 0).address = Nat.pair 0 (Nat.pair 10 0) ∧
    (read w 25).address = Nat.pair 0 (Nat.pair 11 0) := ⟨(pointer_codes w).1,(pointer_codes w).2.1⟩

theorem actual_control_port (w : Nat → F) :
    (read w 42).address = Nat.pair 0 (Nat.pair 12 0) := (pointer_codes w).2.2.1

theorem state_ram_uses_actual_read (w : Nat → F) :
    (write w 1).address = Nat.pair 1 (read w 0).value := (pointer_codes w).2.2.2.1

theorem message_ram_uses_actual_read (w : Nat → F) :
    (write w 26).address = Nat.pair 1 (read w 25).value := (pointer_codes w).2.2.2.2

theorem both_readonly_refreshes (w : Nat → F) (pointer : Fin 2) :
    (write w (pointerSlot pointer)).value = (read w (pointerSlot pointer)).value := readonly_pointer w pointer

theorem all43_register_classification (slot : Fin 43) :
    direct slot = true ↔ slot = 0 ∨ slot = 25 ∨ slot = 42 := direct_slots slot

theorem indirect_spaces (w : Nat → F) (slot : Fin 43) (indirect : direct slot = false) :
    (Nat.unpair (read w slot).address).1 = 1 := ram_space w slot indirect

/-- Pure reference assignments only. NONE is a full worker accepted fixture. -/
def zeroPointers (_ : Nat) : F := 0
def separated (column : Nat) : F := if column = 100 then 128 else 0
def overlapping (column : Nat) : F := if column = 100 then 4 else 0

theorem equal_pointers_alias : (write zeroPointers 1).address = (write zeroPointers 26).address := by decide +kernel

theorem nonzero_message_read : (read separated 25).value = Nat.pair 128 0 ∧ (read separated 25).value ≠ 0 := by decide +kernel

theorem zero_state_pointer_allowed_as_reference : (read separated 0).value = 0 ∧
    (write separated 1).address = Nat.pair 1 0 := by decide +kernel

theorem different_pointer_codes : (read separated 0).value ≠ (read separated 25).value := by decide +kernel

/-- Unequal bases alone do NOT establish full43-port separation. -/
theorem unequal_bases_can_still_overlap : (read overlapping 0).value ≠ (read overlapping 25).value ∧
    (write overlapping 2).address = (write overlapping 26).address := by decide +kernel

def referenceEdge (a b : Fin 3) : Prop := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)
def referenceValue (a : Fin 3) : Nat := if a = 0 then 0 else 9

theorem finite_path : Relation.ReflTransGen referenceEdge (0 : Fin 3) 2 := by
  have first : Relation.ReflTransGen referenceEdge (0 : Fin 3) 1 := .single (Or.inl ⟨rfl,rfl⟩)
  exact first.tail (Or.inr ⟨rfl,rfl⟩)

theorem exact_last_changed_value :
    ∃ prior fresh, referenceEdge prior fresh ∧ referenceValue fresh = referenceValue 2 ∧
      referenceValue fresh ≠ referenceValue prior ∧ Relation.ReflTransGen referenceEdge fresh 2 :=
  last_change referenceEdge referenceValue finite_path rfl (by decide +kernel)

theorem unchanged_suffix_retained : referenceValue 1 = referenceValue 2 ∧ referenceValue 0 ≠ referenceValue 1 := by decide +kernel

theorem actual_main_port (row : Airbender.NativeMixedMemoryOrder.MainRow) (port : Trace.MemoryPort)
    (actual : port ∈ row.ports)
    (changed : (Trace.writeToken row.columns row.assignment port).value ≠ (Trace.readToken row.assignment port).value) :
    port = Airbender.ReducedMachine.NativeMainAuxiliary.mainPort 2 := changed_main_port row port actual changed

theorem complete_active_main_origin {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers) (active : w constraintsABI.multiplicity = 1) :
    ∃ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs,
      row.assignment importedConstraintsTraceColumns.execute = 1 := by
  obtain ⟨_,_,_,_,origin⟩ := native_worker_pointer_origins embed memory ch pc gamma config accepted identity member active
  obtain ⟨row,present,_,_,execution,_⟩ := origin
  exact ⟨row,present,execution⟩
end Airbender.Tests.NativeWorkerPointers
