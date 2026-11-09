import Airbender.Proofs.ReducedMachine.PointerPrefix.Block0
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block1
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block2
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block3
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block4
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block5
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block6
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block7
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block8
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block9
import Airbender.Proofs.ReducedMachine.PointerPrefix.Block10
import Airbender.Review.Trace.Families.ReducedMachine.PointerPrefix
import Airbender.Review.Circuits.ReducedMachine.DelegationSupport
import Airbender.Proofs.ReducedMachine.NativeSparseMain

namespace Airbender.NativePointerPrefixProofs
open Airbender.NativePointerPrefix Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native Airbender.Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

def rows := place assignment NativeSparseMainProofs.idle

theorem body (row : Fin 41) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment row)) (importedConstraints NativeRuntimePool.table) := by
  by_cases h0 : row.val < 4
  · have localBound : row.val - 0 < 4 := by omega
    have same : Block0.index ⟨row.val - 0,localBound⟩ = row := by
      apply Fin.ext
      change 0 + (row.val - 0) = row.val
      omega
    exact same ▸ Block0.body ⟨row.val - 0,localBound⟩
  by_cases h1 : row.val < 8
  · have localBound : row.val - 4 < 4 := by omega
    have same : Block1.index ⟨row.val - 4,localBound⟩ = row := by
      apply Fin.ext
      change 4 + (row.val - 4) = row.val
      omega
    exact same ▸ Block1.body ⟨row.val - 4,localBound⟩
  by_cases h2 : row.val < 12
  · have localBound : row.val - 8 < 4 := by omega
    have same : Block2.index ⟨row.val - 8,localBound⟩ = row := by
      apply Fin.ext
      change 8 + (row.val - 8) = row.val
      omega
    exact same ▸ Block2.body ⟨row.val - 8,localBound⟩
  by_cases h3 : row.val < 16
  · have localBound : row.val - 12 < 4 := by omega
    have same : Block3.index ⟨row.val - 12,localBound⟩ = row := by
      apply Fin.ext
      change 12 + (row.val - 12) = row.val
      omega
    exact same ▸ Block3.body ⟨row.val - 12,localBound⟩
  by_cases h4 : row.val < 20
  · have localBound : row.val - 16 < 4 := by omega
    have same : Block4.index ⟨row.val - 16,localBound⟩ = row := by
      apply Fin.ext
      change 16 + (row.val - 16) = row.val
      omega
    exact same ▸ Block4.body ⟨row.val - 16,localBound⟩
  by_cases h5 : row.val < 24
  · have localBound : row.val - 20 < 4 := by omega
    have same : Block5.index ⟨row.val - 20,localBound⟩ = row := by
      apply Fin.ext
      change 20 + (row.val - 20) = row.val
      omega
    exact same ▸ Block5.body ⟨row.val - 20,localBound⟩
  by_cases h6 : row.val < 28
  · have localBound : row.val - 24 < 4 := by omega
    have same : Block6.index ⟨row.val - 24,localBound⟩ = row := by
      apply Fin.ext
      change 24 + (row.val - 24) = row.val
      omega
    exact same ▸ Block6.body ⟨row.val - 24,localBound⟩
  by_cases h7 : row.val < 32
  · have localBound : row.val - 28 < 4 := by omega
    have same : Block7.index ⟨row.val - 28,localBound⟩ = row := by
      apply Fin.ext
      change 28 + (row.val - 28) = row.val
      omega
    exact same ▸ Block7.body ⟨row.val - 28,localBound⟩
  by_cases h8 : row.val < 36
  · have localBound : row.val - 32 < 4 := by omega
    have same : Block8.index ⟨row.val - 32,localBound⟩ = row := by
      apply Fin.ext
      change 32 + (row.val - 32) = row.val
      omega
    exact same ▸ Block8.body ⟨row.val - 32,localBound⟩
  by_cases h9 : row.val < 40
  · have localBound : row.val - 36 < 4 := by omega
    have same : Block9.index ⟨row.val - 36,localBound⟩ = row := by
      apply Fin.ext
      change 36 + (row.val - 36) = row.val
      omega
    exact same ▸ Block9.body ⟨row.val - 36,localBound⟩
  · have same : Block10.index 0 = row := by
      apply Fin.ext
      change 40 = row.val
      have := row.isLt
      omega
    exact same ▸ Block10.body 0

theorem place_at (activeRows : Fin 41 → Nat → F) (idle : Nat → F) (row : Fin 41) :
    place activeRows idle (blockStart + row.val) = activeRows row := by
  have bound := row.isLt
  unfold place
  rw [dif_pos (by omega)]
  apply congrArg activeRows
  apply Fin.ext
  exact Nat.add_sub_cancel_left blockStart row.val

theorem at_prefix (row : Fin 41) : rows (blockStart + row.val) = assignment row :=
  place_at assignment NativeSparseMainProofs.idle row

theorem before_prefix (i : Nat) (bound : i < blockStart) : rows i = NativeSparseMainProofs.idle := by
  simp only [rows,place]
  rw [dif_neg (by omega)]

theorem ordinary_body (i : Nat) (_bound : i < callerAuxiliaryLayout.traceLength - 1) :
    FlatOperation.ConstraintsHoldFlat (environment (rows i)) (importedConstraints NativeRuntimePool.table) := by
  unfold rows place
  split
  · exact body _
  · exact NativeSparseMainProofs.idle_body

theorem finite_adjacent (row : Fin 40) :
    Airbender.NativeInitializationOrdering.AdjacentAccepted
      (assignment ⟨row.val,by have := row.isLt; omega⟩)
      (assignment ⟨row.val + 1,by have := row.isLt; omega⟩) := by
  fin_cases row <;> constructor <;> decide +kernel

theorem idle_adjacent : Airbender.NativeInitializationOrdering.AdjacentAccepted NativeSparseMainProofs.idle NativeSparseMainProofs.idle := by
  constructor <;> decide +kernel

theorem entry_adjacent : Airbender.NativeInitializationOrdering.AdjacentAccepted NativeSparseMainProofs.idle (assignment 0) := by
  constructor <;> decide +kernel

theorem ordinary_adjacent (i : Nat) (bound : i < callerAuxiliaryLayout.traceLength - 2) :
    Airbender.NativeInitializationOrdering.AdjacentAccepted (rows i) (rows (i + 1)) := by
  by_cases early : i < blockStart
  · rw [before_prefix i early]
    by_cases nextEarly : i + 1 < blockStart
    · rw [before_prefix (i + 1) nextEarly]
      exact idle_adjacent
    · have same : i + 1 = blockStart + (0 : Fin 41).val := by omega
      rw [same,at_prefix]
      exact entry_adjacent
  · have localBound : i - blockStart < 40 := by
      change i < 8388606 at bound
      change ¬ i < 8388566 at early
      change i - 8388566 < 40
      omega
    have left := at_prefix ⟨i - blockStart,by omega⟩
    have right := at_prefix ⟨i - blockStart + 1,by omega⟩
    have l : blockStart + (i - blockStart) = i := by omega
    have r : blockStart + (i - blockStart + 1) = i + 1 := by omega
    simp only [l,r] at left right
    rw [left,right]
    exact finite_adjacent ⟨i - blockStart,localBound⟩

theorem records (index : Fin 40) :
    Airbender.NativeInitializationBoundary.record (assignment ⟨index.val + 1,by have := index.isLt; omega⟩) =
      #v[(NativePointerPrefix.ramAddress index.val : F),0,0,0,167,0] := by
  fin_cases index <;> decide +kernel

theorem nonpadding (index : Fin 40) :
    Airbender.NativeInitializationLedger.paddingRow (assignment ⟨index.val + 1,by have := index.isLt; omega⟩) = false := by
  fin_cases index <;> decide +kernel

theorem first_record : Airbender.NativeInitializationBoundary.record (rows 0) = #v[0,0,0,0,0,0] := by
  rw [before_prefix 0 (by decide +kernel)]
  decide +kernel

theorem last_record : Airbender.NativeInitializationBoundary.record (rows (callerAuxiliaryLayout.traceLength - 2)) = #v[188,0,0,0,167,0] := by
  have last := at_prefix (40 : Fin 41)
  have same : blockStart + (40 : Fin 41).val = callerAuxiliaryLayout.traceLength - 2 := by decide +kernel
  rw [same] at last
  rw [last]
  decide +kernel

def endpoints : Airbender.NativeInitializationBoundary.PublicValues :=
  ⟨Airbender.NativeInitializationBoundary.record (rows 0),
    Airbender.NativeInitializationBoundary.record (rows (callerAuxiliaryLayout.traceLength - 2))⟩

theorem public_endpoints :
    Airbender.NativeInitializationBoundary.EndpointAccepted (rows 0) endpoints.first ∧
    Airbender.NativeInitializationBoundary.EndpointAccepted (rows (callerAuxiliaryLayout.traceLength - 2)) endpoints.oneBeforeLast := by
  constructor <;> intro slot <;> simp [endpoints,Airbender.NativeInitializationBoundary.term]

theorem active_fields (row : Fin 41) : assignment row importedConstraintsTraceColumns.execute = 1 := by
  fin_cases row <;> decide +kernel

theorem first_pointer_write : (mainMemoryKey (assignment 0) 2 true).address = ⟨1,11,0⟩ ∧
    (mainMemoryKey (assignment 0) 2 true).value = #v[128,0] ∧
    (mainMemoryKey (assignment 0) 2 true).time = #v[6,0] := by decide +kernel

theorem caller_fields : csrRequest (assignment 40) = ⟨1,1991,some 0,3⟩ ∧
    Airbender.NativeDelegationSupport.callerKey (assignment 40) = ⟨1991,0,167,0⟩ := by decide +kernel

theorem fixed_endpoints :
    Airbender.NativeInitializationBoundary.EndpointAccepted (rows 0) #v[0,0,0,0,0,0] ∧
    Airbender.NativeInitializationBoundary.EndpointAccepted
      (rows (callerAuxiliaryLayout.traceLength - 2)) #v[188,0,0,0,167,0] := by
  constructor
  · intro slot
    rw [Airbender.NativeInitializationBoundary.term,first_record]
    simp
  · intro slot
    rw [Airbender.NativeInitializationBoundary.term,last_record]
    simp

theorem components : Components assignment NativeSparseMainProofs.idle := by
  exact ⟨ordinary_body,active_fields,ordinary_adjacent,records,nonpadding,
    first_record,last_record,fixed_endpoints,first_pointer_write,caller_fields⟩

theorem fixture : ∃ activeRows idle, Components activeRows idle :=
  ⟨assignment,NativeSparseMainProofs.idle,components⟩
end Airbender.NativePointerPrefixProofs

