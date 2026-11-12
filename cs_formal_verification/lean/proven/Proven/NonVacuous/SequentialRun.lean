module
public import Human.Helpers.Delegation.RVBoundaryMemory
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-! A sequential honest run over a keyed memory, shared by the non-vacuity witnesses of multi-row spans: each
    step reads the current value at its key (a seed or the previous write of that key) and writes a new one. Its
    edges satisfy the logical memory matching (`MemoryAccepted.matching`: seeds and writes are a permutation of
    the final values and reads), and an RV initial image gives the boundary inputs of a native cut. -/

namespace Airbender.NonVacuous

section Run
open scoped List
variable {α β : Type} [DecidableEq β]

/-- The (read, write) edges of a run: each step reads its key's current value, then the key holds the write. -/
def runEdges : (β → α) → List (β × α) → List (α × α)
  | _, [] => []
  | mem, (key, write) :: rest => (mem key, write) :: runEdges (Function.update mem key write) rest

/-- The memory after a run. -/
def runFinal : (β → α) → List (β × α) → β → α
  | mem, [] => mem
  | mem, (key, write) :: rest => runFinal (Function.update mem key write) rest

theorem runEdges_append (mem : β → α) (first second : List (β × α)) :
    runEdges mem (first ++ second) = runEdges mem first ++ runEdges (runFinal mem first) second := by
  induction first generalizing mem with
  | nil => rfl
  | cons step rest ih => obtain ⟨key, write⟩ := step; simp only [List.cons_append, runEdges, runFinal, ih]

theorem runFinal_append (mem : β → α) (first second : List (β × α)) :
    runFinal mem (first ++ second) = runFinal (runFinal mem first) second := by
  induction first generalizing mem with
  | nil => rfl
  | cons step rest ih => obtain ⟨key, write⟩ := step; simp only [List.cons_append, runFinal, ih]

/-- Steps at distinct keys all read the memory before the run. -/
theorem runEdges_of_nodup (mem : β → α) {steps : List (β × α)} (distinct : (steps.map Prod.fst).Nodup) :
    runEdges mem steps = steps.map fun step => (mem step.1, step.2) := by
  induction steps generalizing mem with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨key, write⟩ := step
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at distinct
    simp only [runEdges, List.map_cons, ih _ distinct.2]
    congr 1
    apply List.map_congr_left
    intro other member
    rw [Function.update_of_ne]
    rintro rfl
    exact distinct.1 ⟨other, member, rfl⟩

/-- A key a run does not touch keeps its value. -/
theorem runFinal_of_not_mem (mem : β → α) {steps : List (β × α)} {key : β} (absent : key ∉ steps.map Prod.fst) :
    runFinal mem steps key = mem key := by
  induction steps generalizing mem with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨other, write⟩ := step
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    simp only [runFinal, ih _ absent.2, Function.update_of_ne absent.1]

/-- After a run at distinct keys, a written key holds its write. -/
theorem runFinal_of_mem (mem : β → α) {steps : List (β × α)} (distinct : (steps.map Prod.fst).Nodup)
    {key : β} {write : α} (member : (key, write) ∈ steps) : runFinal mem steps key = write := by
  induction steps generalizing mem with
  | nil => cases member
  | cons step rest ih =>
    obtain ⟨other, value⟩ := step
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at distinct
    rcases List.mem_cons.mp member with same | later
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      rw [runFinal, runFinal_of_not_mem _ (by simpa only [List.mem_map] using distinct.1)]
      exact Function.update_self ..
    · exact ih _ distinct.2 later

/-- Writing `write` at a key of `keys` swaps the key's old value for `write` in the image of `keys`. -/
private theorem update_perm {keys : List β} (nodup : keys.Nodup) (mem : β → α) {key : β} (member : key ∈ keys)
    (write : α) :
    (keys.map mem ++ [write]).Perm (keys.map (Function.update mem key write) ++ [mem key]) := by
  induction keys with
  | nil => cases member
  | cons head rest ih =>
    rw [List.nodup_cons] at nodup
    by_cases same : head = key
    · subst same
      have untouched : rest.map (Function.update mem head write) = rest.map mem :=
        List.map_congr_left fun other present => Function.update_of_ne (by rintro rfl; exact nodup.1 present) ..
      simp only [List.map_cons, Function.update_self, untouched, List.cons_append]
      calc mem head :: (rest.map mem ++ [write])
          _ ~ mem head :: write :: rest.map mem := (List.perm_append_singleton write _).cons _
          _ ~ write :: mem head :: rest.map mem := List.Perm.swap _ _ _
          _ ~ write :: (rest.map mem ++ [mem head]) := ((List.perm_append_singleton _ _).cons _).symm
    · have later : key ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      rw [List.map_cons, List.map_cons, Function.update_of_ne same, List.cons_append, List.cons_append, List.perm_cons]
      exact ih nodup.2 later

/-- The matching of a sequential run: the initial values and the writes are a permutation of the final values and
    the reads, for any run whose keys lie in a duplicate-free `keys`. -/
theorem run_matching {keys : List β} (nodup : keys.Nodup) (mem : β → α) {steps : List (β × α)}
    (inside : ∀ step ∈ steps, step.1 ∈ keys) :
    (keys.map mem ++ (runEdges mem steps).map Prod.snd).Perm
      (keys.map (runFinal mem steps) ++ (runEdges mem steps).map Prod.fst) := by
  induction steps generalizing mem with
  | nil => simp only [runEdges, List.map_nil, runFinal, List.Perm.refl]
  | cons step rest ih =>
    obtain ⟨key, write⟩ := step
    have member : key ∈ keys := inside _ (List.mem_cons_self ..)
    have tail := ih (Function.update mem key write) fun s m => inside s (List.mem_cons_of_mem _ m)
    simp only [runEdges, runFinal, List.map_cons]
    calc keys.map mem ++ write :: (runEdges (Function.update mem key write) rest).map Prod.snd
        = (keys.map mem ++ [write]) ++ (runEdges (Function.update mem key write) rest).map Prod.snd := by simp
      _ ~ (keys.map (Function.update mem key write) ++ [mem key]) ++
            (runEdges (Function.update mem key write) rest).map Prod.snd :=
          (update_perm nodup mem member write).append_right _
      _ ~ (keys.map (Function.update mem key write) ++
            (runEdges (Function.update mem key write) rest).map Prod.snd) ++ [mem key] := by
          simp only [List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
      _ ~ (keys.map (runFinal (Function.update mem key write) rest) ++
            (runEdges (Function.update mem key write) rest).map Prod.fst) ++ [mem key] := tail.append_right _
      _ ~ keys.map (runFinal (Function.update mem key write) rest) ++
            mem key :: (runEdges (Function.update mem key write) rest).map Prod.fst :=
          (List.perm_append_singleton _ _).trans List.perm_middle.symm

end Run

section Image
open Trace Arithmetic
variable {p : Nat}

private theorem initialImageRV_cons {before : RV.State} {cell : Cell} {rest : List Cell} {tokens : List (MemoryToken p)}
    (initialization : initialImageRV before (cell :: rest) = some tokens) :
    ∃ value others, cell.readRV before = some value ∧ initialImageRV before rest = some others ∧
      tokens = cell.initialToken value :: others := by
  simp only [initialImageRV, List.mapM_cons, bind, Option.bind_eq_some_iff, Option.map_eq_some_iff, pure,
    Option.some.injEq] at initialization
  obtain ⟨_, ⟨value, read, rfl⟩, others, image, rfl⟩ := initialization
  exact ⟨value, others, read, image, rfl⟩

/-- An RV initial image is a native cut's boundary image (seed values read from the state). -/
theorem boundary_image {before : RV.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (initialization : initialImageRV before cells = some tokens) :
    Delegation.RVBoundaryImage tokens before cells ∧ ∀ token ∈ tokens, token.time = (0, 0) := by
  induction cells generalizing tokens with
  | nil =>
    simp only [initialImageRV, List.mapM_nil, Option.pure_def, Option.some.injEq] at initialization
    subst initialization
    exact ⟨⟨List.Perm.refl _, fun _ member => by cases member⟩, fun _ member => by cases member⟩
  | cons cell rest ih =>
    obtain ⟨value, others, read, image, rfl⟩ := initialImageRV_cons initialization
    obtain ⟨⟨addresses, values⟩, times⟩ := ih image
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact addresses.cons _
    · intro token member
      rcases List.mem_cons.mp member with rfl | later
      · refine ⟨cell, List.mem_cons_self .., value, rfl, read, ?_⟩
        simp only [Cell.initialToken, MemoryToken.word, Nat.unpair_pair]
      · obtain ⟨other, present, word, code, read', same⟩ := values token later
        exact ⟨other, List.mem_cons_of_mem _ present, word, code, read', same⟩
    · intro token member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact times token later

/-- Readable cells give the initial image of their seeds. -/
theorem initial_image {before : RV.State} {cells : List Cell}
    (readable : ∀ cell ∈ cells, (cell.readRV before).isSome) :
    initialImageRV before cells =
      some (cells.map fun cell => (cell.initialToken ((cell.readRV before).getD 0) : MemoryToken p)) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    obtain ⟨value, read⟩ := Option.isSome_iff_exists.mp (readable cell (List.mem_cons_self ..))
    simp only [initialImageRV, List.mapM_cons, read, Option.map_some, Option.getD_some, List.map_cons] at ih ⊢
    rw [ih fun c member => readable c (List.mem_cons_of_mem _ member)]
    rfl

/-- A seed holds a canonical word. -/
theorem seed_bounded (cell : Cell) (value : BitVec 32) : (cell.initialToken value : MemoryToken p).word.Bounded := by
  have bound := value.isLt
  simp only [Cell.initialToken, MemoryToken.word, Nat.unpair_pair, Word.ofBitVec, Word.Bounded, limbBase]
  omega

/-- A delegation port reads `tok` when its address, previous clock and read limbs are `tok`'s. -/
theorem read_eq [NeZero p] (room : 65536 ≤ p) {w : Nat → ZMod p} {port : MemoryPort} {tok : MemoryToken p} {c0 c1 r0 r1 hi : Nat}
    (previous : port.clock.previous = #v[c0, c1]) (readValue : port.readValue = .u16 #v[r0, r1])
    (address : port.address.code w = tok.address) (time0 : w c0 = ((tok.time.1.val : Nat) : ZMod p))
    (time1 : w c1 = ((0 : Nat) : ZMod p)) (low : w r0 = ((tok.word.lo : Nat) : ZMod p))
    (upper : w r1 = ((hi : Nat) : ZMod p)) (same : hi = tok.word.hi) (high : tok.time.2 = 0)
    (bounded : tok.word.Bounded) : readToken w port = tok := by
  obtain ⟨code, ⟨first, second⟩, value⟩ := tok
  simp only [Word.Bounded, limbBase, MemoryToken.word] at bounded same low upper time0
  simp only at high
  subst high same
  simp only [readToken, rawPair, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, previous, readValue,
    address, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, time0, time1,
    low, upper, ZMod.natCast_zmod_val, Nat.cast_zero, MemoryToken.mk.injEq, true_and]
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt
    (by omega), Nat.pair_unpair]

/-- A token whose value pairs two small field limbs. -/
theorem token_word (room : 65536 ≤ p) {tok : MemoryToken p} {a b : Nat}
    (value : tok.value = Nat.pair ((a : Nat) : ZMod p).val ((b : Nat) : ZMod p).val) (ha : a < 65536)
    (hb : b < 65536) : tok.word = ⟨a, b⟩ := by
  rw [MemoryToken.word, value, ZMod.val_natCast_of_lt (by omega),
    ZMod.val_natCast_of_lt (by omega), Nat.unpair_pair]

/-- RV memory inputs at a seed cut give the boundary inputs there (seed clocks are zero). -/
theorem boundary_inputs {data : Delegation.MemoryData p} {before : RV.State} {cells : List Cell}
    (inputs : Delegation.RVMemoryInputs data before cells) : Delegation.RVBoundaryMemoryInputs data before cells :=
  have image := boundary_image inputs.initialization
  ⟨image.1, inputs.distinct, fun token member => by
    rw [image.2 token member]
    simp only [timeOfPair, ZMod.val_zero, Timestamp.Bounded, timestampBase]
    decide, inputs.clockRoom, inputs.invocationHigh⟩

end Image

end Airbender.NonVacuous
