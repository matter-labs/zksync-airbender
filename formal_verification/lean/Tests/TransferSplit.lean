import Airbender.Proofs.Trace.TransferSplit

namespace Tests.TransferSplit
open Airbender.Trace Airbender.Trace.Proofs
open Airbender.Reference.RiscV.Sail
set_option warningAsError true

private def seedA : MemoryToken 17 := (Cell.register 1).initialToken 0
private def seedB : MemoryToken 17 := (Cell.register 2).initialToken 5
private def middleA : MemoryToken 17 := ⟨seedA.address, (3, 0), Nat.pair 31 0⟩
private def finalA : MemoryToken 17 := ⟨seedA.address, (6, 0), Nat.pair 42 0⟩
private def finalB : MemoryToken 17 := ⟨seedB.address, (3, 0), Nat.pair 7 0⟩

private def data : Transfer.Data 17 :=
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

private def cells : List Cell := [.register 1, .register 2]
private def before : Airbender.Reference.RiscV.Sail.State where
  regs := Std.ExtDHashMap.emptyWithCapacity |>.insert .x1 (0 : BitVec 32) |>.insert .x2 (5 : BitVec 32)
  mem := Std.ExtHashMap.emptyWithCapacity
  tags := ()
  cycleCount := 0
  sailOutput := #[]

private theorem inputs : Transfer.Inputs data before cells := by
  have readA : (Cell.register 1).read before = .ok 0 before := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have readB : (Cell.register 2).read before = .ok 5 before := by
    apply read_register
    simp [before]
  refine ⟨?_, by decide +kernel⟩
  simp only [cells, initialImage, List.mapM_cons, List.mapM_nil, readA, readB, bind, Option.bind, pure]
  rfl

theorem native_cut_reads : ∃ events after,
    events.Perm ((Transfer.beforeSteps data 3).map transferEvent) ∧
    SailHistory cells events before after ∧
    (Cell.register 1).read after = .ok 31 after ∧
    (Cell.register 2).read after = .ok 7 after := by
  have nonzero : ∀ edge ∈ data.steps, edge.1.address ≠ (Cell.register 0).addressCode := by
    intro edge member
    simp [data] at member
    rcases member with rfl | rfl | rfl
    all_goals decide +kernel
  have aligned : ∀ cell ∈ cells, cell.Aligned := by
    intro cell member
    simp [cells] at member
    rcases member with rfl | rfl
    all_goals trivial
  obtain ⟨middle, events, after, earlier, _, native, _, history, reads⟩ :=
    Transfer.split_sail_state accepted inputs aligned
      (fun edge member same => False.elim (nonzero edge member same)) 3
  have boundary := boundary_correct earlier
  obtain ⟨cellA, _, codeA, readA⟩ := reads middleA
    (boundary.mem_iff.mpr (List.mem_cons_self))
  obtain ⟨cellB, _, codeB, readB⟩ := reads finalB
    (boundary.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have equalA : cellA = .register 1 := cell_address_injective codeA
  have equalB : cellB = .register 2 := cell_address_injective codeB
  subst cellA
  subst cellB
  have wordA : memoryWord middleA.value = (31 : BitVec 32) := by decide +kernel
  have wordB : memoryWord finalB.value = (7 : BitVec 32) := by decide +kernel
  rw [wordA] at readA
  rw [wordB] at readB
  exact ⟨events, after, native, history, readA, readB⟩

theorem suffix_read_rejected :
    ¬ Transfer.Facts (⟨[middleA, finalB], [finalA, finalB],
      [({middleA with value := Nat.pair 32 0}, finalA)]⟩ : Transfer.Data 17) := by
  intro facts
  have rejected : ¬ ([middleA, finalB] ++ [finalA]).Perm
      ([finalA, finalB] ++ [{middleA with value := Nat.pair 32 0}]) := by decide +kernel
  exact rejected facts.matching

theorem native_suffix_execution : ∃ (middle : List (MemoryToken 17))
    (earlierEvents laterEvents : List MemoryAccess) (atCut after : State),
    middle.Perm [middleA, finalB] ∧
    (middle.map MemoryToken.time).Perm [(3, 0), (3, 0)] ∧
    earlierEvents.Perm ((Transfer.beforeSteps data 3).map transferEvent) ∧
    laterEvents.Perm ((Transfer.afterSteps data 3).map transferEvent) ∧
    SailHistory cells earlierEvents before atCut ∧ SailHistory cells laterEvents atCut after ∧
    SailHistory cells (laterEvents ++ earlierEvents) before after ∧
    (Cell.register 1).read atCut = .ok 31 atCut ∧
    (Cell.register 1).read after = .ok 42 after ∧
    (Cell.register 2).read after = .ok 7 after := by
  have nonzero : ∀ edge ∈ data.steps, edge.1.address ≠ (Cell.register 0).addressCode := by
    intro edge member
    simp [data] at member
    rcases member with rfl | rfl | rfl
    all_goals decide +kernel
  have aligned : ∀ cell ∈ cells, cell.Aligned := by
    intro cell member
    simp [cells] at member
    rcases member with rfl | rfl
    all_goals trivial
  obtain ⟨middle, earlierEvents, laterEvents, atCut, after, earlier, _, prefixPerm, suffixPerm,
    _, _, prefixHistory, suffixHistory, combined, reads, final⟩ :=
    Transfer.split_sail_execution accepted inputs aligned
      (fun edge member same => False.elim (nonzero edge member same)) 3
  have boundary := boundary_correct earlier
  have clocks : (middle.map MemoryToken.time).Perm [(3, 0), (3, 0)] := by
    simpa only [List.map_cons, List.map_nil, middleA, finalB] using boundary.map MemoryToken.time
  obtain ⟨first, _, firstCode, firstRead⟩ := reads middleA
    (boundary.mem_iff.mpr List.mem_cons_self)
  have firstCell : first = .register 1 := cell_address_injective firstCode
  subst first
  obtain ⟨lastA, _, codeA, readA⟩ := final finalA (by simp [data])
  have cellA : lastA = .register 1 := cell_address_injective codeA
  subst lastA
  obtain ⟨lastB, _, codeB, readB⟩ := final finalB (by simp [data])
  have cellB : lastB = .register 2 := cell_address_injective codeB
  subst lastB
  have wordMiddle : memoryWord middleA.value = (31 : BitVec 32) := by decide +kernel
  have wordA : memoryWord finalA.value = (42 : BitVec 32) := by decide +kernel
  have wordB : memoryWord finalB.value = (7 : BitVec 32) := by decide +kernel
  rw [wordMiddle] at firstRead
  rw [wordA] at readA
  rw [wordB] at readB
  exact ⟨middle, earlierEvents, laterEvents, atCut, after, boundary, clocks, prefixPerm, suffixPerm,
    prefixHistory, suffixHistory, combined, firstRead, readA, readB⟩

end Tests.TransferSplit
