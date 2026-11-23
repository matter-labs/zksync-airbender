module
public import Human.Trace.WritesRangeChecked
public import Human.Circuits.InitsTeardowns.Theorems
public import Proven.Trace.Values
public import Proven.Defs.Helpers.Memory.Ports

@[expose] public section

/-! Write sites: a per-port write rule gives `WritesRangeChecked` of a row's memory steps; `Init` tuples write the zero
    word; under `MemoryArgumentReadsBounded`, bounded writes bound every teardown. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- A per-port rule "every read bounded gives every write bounded" is `WritesRangeChecked` of the steps. -/
theorem writesRangeChecked_of_ports {p : Nat} {ports : Array MemoryPort} {read write : MemoryPort → MemoryToken p}
    (rule : (∀ port ∈ ports, (read port).word.Bounded) → ∀ port ∈ ports, (write port).word.Bounded) :
    WritesRangeChecked (ports.toList.map fun port => (read port, write port)) := by
  intro reads step member
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp member
  exact rule (fun source sourceMember =>
    reads _ (List.mem_map.mpr ⟨source, Array.mem_toList_iff.mpr sourceMember, rfl⟩)) port
    (Array.mem_toList_iff.mp present)

/-- A row's time-ordered write rule gives `WritesRangeChecked` of its memory steps. -/
theorem writesRangeChecked_of_rule {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    {row : Row p Kind} (rule : RowWriteBoundsFromReads row) : WritesRangeChecked row.memorySteps :=
  writesRangeChecked_of_ports fun reads port present => rule port present fun source sourceMember _ =>
    reads source sourceMember

/-- Writes of rows whose every port write is bounded. -/
theorem row_writes_bounded {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] {rows : List (Row p Kind)}
    (bounded : ∀ row ∈ rows, ∀ port ∈ row.ports, (writeToken row.columns row.assignment port).word.Bounded) :
    ∀ token ∈ rows.flatMap Row.writes, token.word.Bounded := by
  intro token member
  obtain ⟨row, rowMember, written⟩ := List.mem_flatMap.mp member
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp written
  exact bounded row rowMember port (Array.mem_toList_iff.mp present)

end Airbender.Trace.Proofs

namespace Airbender.InitsTeardowns.Proofs
open Trace Arithmetic

/-- Every `Init` tuple writes the zero word. -/
theorem init_bounded {p : Nat} {layout : Layout} (w : Witness p layout) :
    ∀ token ∈ w.initTokens, token.word.Bounded := by
  intro token member
  simp only [Witness.initTokens, initTokens, List.mem_flatMap, List.mem_map] at member
  obtain ⟨_, _, _, _, rfl⟩ := member
  simp [initToken, MemoryToken.word, Word.Bounded, limbBase]

/-- Under the open item, bounded writes bound every teardown tuple. -/
theorem teardowns_bounded {p : Nat} {layout : Layout} {instances : List (Witness p layout)}
    {writes : List (MemoryToken p)} (reads : MemoryArgumentReadsBounded instances writes)
    (bounded : ∀ token ∈ writes, token.word.Bounded) :
    ∀ w ∈ instances, ∀ token ∈ w.teardownTokens, token.word.Bounded := by
  intro w member token torn
  obtain ⟨write, source, same⟩ := reads w member token torn
  have word : token.word = write.word := by simp only [MemoryToken.word, same]
  rw [word]
  rcases List.mem_append.mp source with init | written
  · obtain ⟨v, vMember, initMember⟩ := List.mem_flatMap.mp init
    exact init_bounded v write initMember
  · exact bounded write written

end Airbender.InitsTeardowns.Proofs
