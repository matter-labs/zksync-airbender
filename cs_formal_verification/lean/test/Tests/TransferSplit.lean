module
public import Slop.Trace.TransferSplit
public import Slop.Trace.TransferBoundary

@[expose] public section

namespace Tests.TransferSplit
open Airbender.Trace Airbender.Trace.Proofs
set_option warningAsError true

def seedA : MemoryToken 17 := (Cell.register 1).initialToken 0
def seedB : MemoryToken 17 := (Cell.register 2).initialToken 5
def middleA : MemoryToken 17 := ⟨seedA.address, (3, 0), Nat.pair 31 0⟩
def finalA : MemoryToken 17 := ⟨seedA.address, (6, 0), Nat.pair 42 0⟩
def finalB : MemoryToken 17 := ⟨seedB.address, (3, 0), Nat.pair 7 0⟩

def data : Transfer.Data 17 :=
  ⟨[seedA, seedB], [finalA, finalB], [(middleA, finalA), (seedB, finalB), (seedA, middleA)]⟩

private theorem accepted : Transfer.Facts data := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  all_goals
    intro edge member
    simp [data] at member
    rcases member with rfl | rfl | rfl
  all_goals decide +kernel

private theorem boundary_correct {middle : List (MemoryToken 17)}
    (earlier : Transfer.Facts ⟨data.initial, middle, Transfer.beforeSteps data 3⟩) :
    middle.Perm [middleA, finalB] := by
  have expected : (data.initial ++ (Transfer.beforeSteps data 3).map Prod.snd).Perm
      ([middleA, finalB] ++ (Transfer.beforeSteps data 3).map Prod.fst) := by decide +kernel
  exact (List.perm_append_right_iff _).mp (earlier.matching.symm.trans expected)

theorem timestamp_cut : ∃ middle : List (MemoryToken 17),
    Transfer.Facts ⟨data.initial, middle, Transfer.beforeSteps data 3⟩ ∧
    Transfer.Facts ⟨middle, data.terminal, Transfer.afterSteps data 3⟩ ∧
    middle.Perm [middleA, finalB] := by
  obtain ⟨middle, earlier, later⟩ := Transfer.split_at accepted 3
  exact ⟨middle, earlier, later, boundary_correct earlier⟩

theorem future_value_rejected :
    ¬ (data.initial ++ (Transfer.beforeSteps data 3).map Prod.snd).Perm
      ([finalA, finalB] ++ (Transfer.beforeSteps data 3).map Prod.fst) := by decide +kernel

theorem suffix_read_rejected :
    ¬ Transfer.Facts (⟨[middleA, finalB], [finalA, finalB],
      [({middleA with value := Nat.pair 32 0}, finalA)]⟩ : Transfer.Data 17) := by
  intro facts
  have rejected : ¬ ([middleA, finalB] ++ [finalA]).Perm
      ([finalA, finalB] ++ [{middleA with value := Nat.pair 32 0}]) := by decide +kernel
  exact rejected facts.matching

end Tests.TransferSplit
