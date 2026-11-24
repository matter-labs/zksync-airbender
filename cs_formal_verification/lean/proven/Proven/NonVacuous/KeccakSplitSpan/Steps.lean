module
public import Proven.NonVacuous.KeccakSplitSpan.Memory
public import Proven.NonVacuous.KeccakSplitSpan.Keys
public import Proven.KeccakSplit.RowCommon

@[expose] public section

/-! The span invariant and one call's step, for any worker: under the invariant `Inv` (tokens at their cells, each
    key's clock the write clock of the last call that touched it, canonical words, the control word of the call in
    x10 and the pointer in x11), a row whose ports read their keys' tokens and write canonical words at clock
    `3 + 4 k` (`RowFacts`) has the sequential run's edges as its memory steps, and the memory after it satisfies the
    invariant before the next call. Also the port lemmas the three workers' `RowFacts` use. -/

namespace Airbender.NonVacuous.KeccakSplitSpan
open Arithmetic Trace Keccak.Split

local notation "P" => babyBearModulus

/-- The span invariant before call `k`. -/
structure Inv (mem : Memory) (k : Nat) : Prop where
  address : ∀ key < 62, (mem key).address = (cellOf key).addressCode
  clock : ∀ key < 62, (mem key).time.1 = ((clockOf (lastTouch k key) : Nat) : ZMod P)
  high : ∀ key < 62, (mem key).time.2 = 0
  words : ∀ key < 62, (mem key).word.Bounded
  control : k < 361 → (mem 0).word = ⟨controlAt k, 0⟩
  pointer : (mem 1).word = ⟨0, 64⟩

/-- What a worker's honest row of call `k` does with the memory (proven per worker): its ports read their keys'
    tokens, write at the invocation clock plus two, and write canonical words, the next control word to x10 and the
    pointer back to x11. -/
structure RowFacts (mem : Memory) (k : Nat) : Prop where
  size : (mem.row k).ports.size = portCount k
  reads : ∀ j (h : j < portCount k),
    readToken (mem.row k).assignment ((mem.row k).ports[j]'(size ▸ h)) = mem (portKey k j)
  offsets : ∀ j (h : j < portCount k), ((mem.row k).ports[j]'(size ▸ h)).clock.offset = 2
  invocation : (mem.row k).columns.invocation = #v[1, 2]
  clockLow : (mem.row k).assignment 1 = ((1 + 4 * k : Nat) : ZMod P)
  clockHigh : (mem.row k).assignment 2 = ((0 : Nat) : ZMod P)
  writes : ∀ j (h : j < portCount k), ((mem.row k).writeToken ((mem.row k).ports[j]'(size ▸ h))).word.Bounded ∧
    (j = 0 → ((mem.row k).writeToken ((mem.row k).ports[j]'(size ▸ h))).word = ⟨bump (controlAt k), 0⟩) ∧
    (j = 1 → ((mem.row k).writeToken ((mem.row k).ports[j]'(size ▸ h))).word = ⟨0, 64⟩)

/-- `RowFacts` from the same facts about a row equal to the call's row. -/
theorem RowFacts.of_row {mem : Memory} {k : Nat} {r : Native.Row P} (row : mem.row k = r)
    (size : r.ports.size = portCount k)
    (reads : ∀ j (h : j < portCount k), readToken r.assignment (r.ports[j]'(size ▸ h)) = mem (portKey k j))
    (offsets : ∀ j (h : j < portCount k), (r.ports[j]'(size ▸ h)).clock.offset = 2)
    (invocation : r.columns.invocation = #v[1, 2]) (clockLow : r.assignment 1 = ((1 + 4 * k : Nat) : ZMod P))
    (clockHigh : r.assignment 2 = ((0 : Nat) : ZMod P))
    (writes : ∀ j (h : j < portCount k), (r.writeToken (r.ports[j]'(size ▸ h))).word.Bounded ∧
      (j = 0 → (r.writeToken (r.ports[j]'(size ▸ h))).word = ⟨bump (controlAt k), 0⟩) ∧
      (j = 1 → (r.writeToken (r.ports[j]'(size ▸ h))).word = ⟨0, 64⟩)) : RowFacts mem k := by
  subst row
  exact ⟨size, reads, offsets, invocation, clockLow, clockHigh, writes⟩

/-- Every key a call accesses is one of the span's keys. -/
theorem portKey_lt {k j : Nat} (h : j < portCount k) : portKey k j < 62 :=
  portKeys_lt (List.mem_map.mpr ⟨j, List.mem_range.mpr h, rfl⟩)

/-- Under the invariant, call `k`'s inputs are valid. -/
theorem valid_of_inv {mem : Memory} {k : Nat} (inv : Inv mem k) (call : k < 361) : (mem.input k).Valid where
  call := call
  pointer := by
    show (mem 1).word.Bounded ∧ (mem 1).word.lo % 256 = 0
    rw [inv.pointer]
    exact ⟨⟨by decide, by decide⟩, by decide⟩
  words j h := inv.words _ (portKey_lt h)
  invocation := by
    show (1 + 4 * k) % 4 = 1
    omega
  room := by
    show 1 + 4 * k + 2 < timestampBase
    simp only [timestampBase]
    omega

/-- A read-only port writes back the word it reads. -/
theorem readonly_word {r : Native.Row P} {port : MemoryPort} (readonly : port.writeValue = none) :
    (r.writeToken port).word = (readToken r.assignment port).word := by
  simp only [Native.Row.writeToken, readToken, MemoryPort.writeCode, MemoryPort.readCode, readonly,
    Option.getD_none, MemoryToken.word]

/-- The address code of a half of a state slot below 30. -/
theorem lane_code {s h : Nat} (hs : s < 30) (hh : h < 2) :
    (cellOf (2 + 2 * s + h)).addressCode = Nat.pair 1 (Nat.pair (8 * s + 4 * h) 64) := by
  have key : 2 + 2 * s + h = (2 * s + h) + 2 := by omega
  have slot : (2 * s + h) / 2 % 31 = s := by omega
  have base : pointerBits = BitVec.ofNat 32 (0 + 65536 * 64) := by decide
  have code := RowProofs.lane_cell_code (lo := 0) (hi := 64) (slot := s) (c := 4 * h) (by decide) (by decide)
    (by decide) (by omega) (by omega)
  rw [key]
  simp only [cellOf, Call.laneCell, slot, base]
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · simpa using code.symm
  · simpa using code.symm

/-- A lane port reads a token at its slot's cell, given the pointer `0x400000` in its base columns. -/
theorem lane_read {w : Nat → ZMod P} {port : MemoryPort} {ip : Verification.IndirectPort} {tok : MemoryToken P}
    {c0 c1 r0 r1 b0 b1 o s h : Nat}
    (previous : port.clock.previous = #v[c0, c1]) (readValue : port.readValue = .u16 #v[r0, r1])
    (address : port.address = .indirect ip) (base : ip.baseColumns = #v[b0, b1]) (scale : ip.scale = 8)
    (offset : ip.offsetColumn = some o) (constant : ip.constant = 4 * h)
    (lo : w b0 = ((0 : Nat) : ZMod P)) (hi : w b1 = ((64 : Nat) : ZMod P)) (slot : w o = ((s : Nat) : ZMod P))
    (time0 : w c0 = ((tok.time.1.val : Nat) : ZMod P)) (time1 : w c1 = ((0 : Nat) : ZMod P))
    (low : w r0 = ((tok.word.lo : Nat) : ZMod P)) (upper : w r1 = ((tok.word.hi : Nat) : ZMod P))
    (code : tok.address = (cellOf (2 + 2 * s + h)).addressCode) (stamp : tok.time.2 = 0)
    (bounded : tok.word.Bounded) (hs : s < 30) (hh : h < 2) : readToken w port = tok := by
  refine read_eq (by decide) previous readValue ?_ time0 time1 low upper rfl stamp bounded
  rw [code, lane_code hs hh, address]
  have sum : w b0 + ((8 : Nat) : ZMod P) * w o + ((4 * h : Nat) : ZMod P) = ((8 * s + 4 * h : Nat) : ZMod P) := by
    rw [lo, slot]
    push_cast
    ring
  simp only [MemoryAddress.code, Verification.IndirectPort.rawAddress, base, scale, offset, constant,
    Option.elim, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [sum, hi, ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega),
    ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega)]

/-- A register port reads the token at its register. -/
theorem register_read {w : Nat → ZMod P} {port : MemoryPort} {tok : MemoryToken P} {c0 c1 r0 r1 : Nat}
    (previous : port.clock.previous = #v[c0, c1])
    (readValue : port.readValue = .u16 #v[r0, r1]) (address : port.address.code w = tok.address)
    (time0 : w c0 = ((tok.time.1.val : Nat) : ZMod P)) (time1 : w c1 = ((0 : Nat) : ZMod P))
    (low : w r0 = ((tok.word.lo : Nat) : ZMod P)) (upper : w r1 = ((tok.word.hi : Nat) : ZMod P))
    (stamp : tok.time.2 = 0) (bounded : tok.word.Bounded) : readToken w port = tok :=
  read_eq (by decide) previous readValue address time0 time1 low upper rfl stamp bounded

variable {mem : Memory} {k : Nat}

theorem step_keys (mem : Memory) (k : Nat) (facts : RowFacts mem k) : (mem.steps k).map Prod.fst = portKeys k :=
  List.map_fst_zip (by simp [portKeys, facts.size])

/-- The row's memory steps are the run's edges from the memory before it. -/
theorem edges (facts : RowFacts mem k) : (mem.row k).memorySteps = runEdges mem (mem.steps k) := by
  rw [runEdges_of_nodup mem (by rw [step_keys mem k facts]; exact portKeys_nodup k)]
  apply List.ext_getElem
  · simp [Native.Row.memorySteps, Memory.steps, portKeys, facts.size]
  · intro n first second
    have bound : n < portCount k := by simpa [Native.Row.memorySteps, facts.size] using first
    simp only [Native.Row.memorySteps, Memory.steps, List.getElem_map, List.getElem_zip, Array.getElem_toList,
      portKeys, List.getElem_range]
    exact Prod.ext (facts.reads n bound) rfl

theorem bump_next : ∀ k < 360, bump (Keccak.Split.controlAt k) = Keccak.Split.controlAt (k + 1) := by
  decide +kernel

/-- The invariant holds after the row, before the next call. -/
theorem next (inv : Inv mem k) (facts : RowFacts mem k) (call : k < 361) :
    Inv (runFinal mem (mem.steps k)) (k + 1) := by
  have nodup : ((mem.steps k).map Prod.fst).Nodup := by rw [step_keys mem k facts]; exact portKeys_nodup k
  have length : (portKeys k).length = portCount k := by simp [portKeys]
  have written (j : Nat) (h : j < portCount k) : runFinal mem (mem.steps k) (portKey k j) =
      (mem.row k).writeToken ((mem.row k).ports[j]'(facts.size ▸ h)) := by
    refine runFinal_of_mem mem nodup (List.mem_iff_getElem.mpr ⟨j, ?_, ?_⟩)
    · simp [Memory.steps, portKeys, facts.size, h]
    · simp [Memory.steps, portKeys]
  have untouched (key : Nat) (absent : key ∉ portKeys k) : runFinal mem (mem.steps k) key = mem key :=
    runFinal_of_not_mem mem (by rw [step_keys mem k facts]; exact absent)
  have split (key : Nat) : (∃ j, ∃ h : j < portCount k, key = portKey k j) ∨ key ∉ portKeys k := by
    by_cases present : key ∈ portKeys k
    · obtain ⟨j, h, rfl⟩ := List.mem_map.mp present
      exact Or.inl ⟨j, List.mem_range.mp h, rfl⟩
    · exact Or.inr present
  have inside (j : Nat) (h : j < portCount k) : portKey k j < 62 :=
    portKeys_lt (List.mem_map.mpr ⟨j, List.mem_range.mpr h, rfl⟩)
  have touched (j : Nat) (h : j < portCount k) : lastTouch (k + 1) (portKey k j) = some k := by
    simp only [lastTouch, List.mem_map.mpr ⟨j, List.mem_range.mpr h, rfl⟩, portKeys, ↓reduceIte]
  have kept (key : Nat) (absent : key ∉ portKeys k) : lastTouch (k + 1) key = lastTouch k key := by
    simp only [lastTouch, absent, ↓reduceIte]
  have address (j : Nat) (h : j < portCount k) :
      ((mem.row k).writeToken ((mem.row k).ports[j]'(facts.size ▸ h))).address = (mem (portKey k j)).address := by
    have same := congrArg MemoryToken.address (facts.reads j h)
    exact same
  have time (j : Nat) (h : j < portCount k) :
      ((mem.row k).writeToken ((mem.row k).ports[j]'(facts.size ▸ h))).time =
        (((clockOf (some k) : Nat) : ZMod P), 0) := by
    simp only [Native.Row.writeToken, rawPair, facts.invocation, facts.offsets j h, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, facts.clockLow, facts.clockHigh,
      clockOf, Nat.cast_zero, Prod.mk.injEq, and_true]
    push_cast
    ring
  constructor
  · intro key small
    rcases split key with ⟨j, h, rfl⟩ | absent
    · rw [written j h, address j h]
      exact inv.address _ small
    · rw [untouched key absent]
      exact inv.address key small
  · intro key small
    rcases split key with ⟨j, h, rfl⟩ | absent
    · rw [written j h, time j h, touched j h]
    · rw [untouched key absent, kept key absent]
      exact inv.clock key small
  · intro key small
    rcases split key with ⟨j, h, rfl⟩ | absent
    · rw [written j h, time j h]
    · rw [untouched key absent]
      exact inv.high key small
  · intro key small
    rcases split key with ⟨j, h, rfl⟩ | absent
    · rw [written j h]
      exact (facts.writes j h).1
    · rw [untouched key absent]
      exact inv.words key small
  · intro more
    have h : 0 < portCount k := by unfold portCount; omega
    have first : runFinal mem (mem.steps k) 0 = _ := written 0 h
    rw [first, (facts.writes 0 h).2.1 rfl, bump_next k (by omega)]
  · have h : 1 < portCount k := by unfold portCount; omega
    have second : runFinal mem (mem.steps k) 1 = _ := written 1 h
    rw [second]
    exact (facts.writes 1 h).2.2 rfl

end Airbender.NonVacuous.KeccakSplitSpan
