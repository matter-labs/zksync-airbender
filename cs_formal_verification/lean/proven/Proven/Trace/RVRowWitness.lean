module
public import Human.Helpers.Context.RVRowModel
public import Human.Helpers.Context.RVInterfaces

@[expose] public section

/-! Family-independent parts of the per-row non-vacuity witnesses (`Trace.RVRowSatisfiable`): one-row pooled traces
    over all 32 registers, seeded from an `RV.State`, with a one-entry program. Each family supplies its row, the
    constraint check, the touched seed tokens and its program entry. -/

namespace Airbender.Trace.Witness
open Arithmetic
open scoped List

/-- The 32 register indices, in order. -/
def registerIndices : List (BitVec 5) := (List.finRange 32).map BitVec.ofFin

/-- All 32 registers as public cells, in order. -/
def registerCells : List Cell := registerIndices.map Cell.register

theorem register_mem (index : BitVec 5) : Cell.register index ∈ registerCells :=
  List.mem_map.mpr ⟨index, List.mem_map.mpr ⟨index.toFin, List.mem_finRange _, rfl⟩, rfl⟩

theorem registerCells_nodup : registerCells.Nodup :=
  ((List.nodup_finRange 32).map fun _ _ h => BitVec.ofFin.inj h).map fun _ _ h => Cell.register.inj h

theorem registerCells_aligned : ∀ cell ∈ registerCells, cell.Aligned := by
  intro cell member
  obtain ⟨index, -, rfl⟩ := List.mem_map.mp member
  trivial

/-- The seed tokens of the 32 registers of `s`. -/
def registerSeeds {p : Nat} (s : RV.State) : List (MemoryToken p) :=
  registerIndices.map fun index => (Cell.register index).initialToken (s.getReg index)

theorem registers_image {p : Nat} (s : RV.State) (indices : List (BitVec 5)) :
    initialImageRV (p := p) s (indices.map Cell.register) =
      some (indices.map fun index => (Cell.register index).initialToken (s.getReg index)) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [initialImageRV, List.map_cons, List.mapM_cons, Cell.readRV, Option.map_some] at ih ⊢
    rw [ih]
    rfl

theorem registerSeeds_image {p : Nat} (s : RV.State) :
    initialImageRV (p := p) s registerCells = some (registerSeeds s) :=
  registers_image s registerIndices

theorem registerSeeds_bounded {p : Nat} [Fact p.Prime] (s : RV.State) :
    ∀ token ∈ registerSeeds (p := p) s, (timeOfPair token.time).Bounded := by
  intro token member
  obtain ⟨index, -, rfl⟩ := List.mem_map.mp member
  simp only [Cell.initialToken, timeOfPair, ZMod.val_zero]
  exact ⟨by decide, by decide⟩

/-- Memory matching of a one-row trace: the seeds are the row's reads plus untouched tokens `rest`, which the
    terminal tokens keep after the row's writes. -/
theorem memory_perm {α : Type} {initial reads writes rest : List α} (seeds : initial.Perm (reads ++ rest)) :
    (initial ++ writes).Perm ((writes ++ rest) ++ reads) := by
  calc (initial ++ writes).Perm ((reads ++ rest) ++ writes) := seeds.append_right writes
    _ ~ (rest ++ writes) ++ reads := by
      simpa only [List.append_assoc] using List.perm_append_comm (l₁ := reads) (l₂ := rest ++ writes)
    _ ~ (writes ++ rest) ++ reads := List.perm_append_comm.append_right reads

/-- State matching of a one-row trace that starts at the row's start and ends at its finish. -/
theorem states_perm {p : Nat} {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) :
    [row.start, row.finish].Perm [row.finish, row.start] :=
  List.Perm.swap _ _ []

/-- In a one-row trace, the row's pre-state is the starting state at the row's start PC. -/
theorem row_position {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] {trace : Data p Kind}
    {row : Row p Kind} (rows : trace.rows = [row]) (initial : RV.State) (cells : List Cell) :
    RVRowPosition trace initial cells row { initial with pc := row.start.word.toBitVec } :=
  ⟨[], [], initial, by rw [rows]; exact List.Perm.refl _, List.pairwise_singleton _ _,
    RVWriteHistory.nil initial, rfl⟩

/-- A query equal to a program entry's query of the right family is in the family's decoder table (the converse
    of `Proofs.rv_decoder_member`). -/
theorem decoder_contains {Kind : Type} [DecidableEq Kind] {p : Nat} [Fact p.Prime]
    {program : List (RVProgramEntry Kind)} {family : Kind} {query : Vector (ZMod p) 9}
    {entry : RVProgramEntry Kind} (member : entry ∈ program) (selected : entry.data.family = family)
    (equal : query = entry.query) : (rvDecoderTable program family).Contains #[] query := by
  have filtered : entry ∈ program.filter (fun entry => entry.data.family == family) := by
    simp [member, selected]
  obtain ⟨i, index⟩ := List.mem_iff_get.mp filtered
  exact ⟨i, equal.trans (congrArg RVProgramEntry.query index).symm⟩

/-- A one-row trace is decoded by a program holding the row's entry. -/
theorem decoded {p : Nat} [Fact p.Prime] {trace : PooledTrace p} {row : Row p PooledFamily}
    {program : List RVPooledProgramEntry} {entry : RVPooledProgramEntry} (rows : trace.rows = [row])
    (member : entry ∈ program) (selected : entry.data.family = row.family) (equal : row.decoderQuery = entry.query) :
    RVPooledDecoded trace program := by
  intro actual present
  rw [rows, List.mem_singleton] at present
  subst actual
  exact decoder_contains member selected equal

/-- The program image of one ROM address. -/
theorem program_image {Kind : Type} {projection : RV.Instr → Option (DecoderData Kind)} {s : RV.State}
    {pc : BitVec 32} {entry : RVProgramEntry Kind} (equal : rvProgramEntryWith projection s pc = some entry) :
    rvProgramImageWith projection s [pc] = some [entry] := by
  simp only [rvProgramImageWith, List.mapM_cons, List.mapM_nil, equal]
  rfl

end Airbender.Trace.Witness
