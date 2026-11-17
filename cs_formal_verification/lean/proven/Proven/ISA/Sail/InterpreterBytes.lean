import Human.ISA.Sail.Interpreter

/-! Byte reads and writes of `runSail` and of lean-sail's sequential interpreter. -/

open Sail Sail.ArchSem SailRV32 Human

namespace Proven.Interpreter
open Airbender

/-- A width cast keeps every bit. -/
theorem getLsbD_rec {m k : Nat} (widths : m = k) (value : BitVec m) (index : Nat) :
    (widths ▸ value : BitVec k).getLsbD index = value.getLsbD index := by
  subst widths
  rfl

/-- `writeBytes` stores byte `a - addr` of the value at each address `a` of the written range. -/
theorem writeBytes_apply (mem : Nat → BitVec 8) (size : Nat) :
    ∀ (addr : Nat) (value : BitVec (8 * size)) (a : Nat),
      writeBytes mem addr size value a =
        if addr ≤ a ∧ a < addr + size then value.extractLsb' (8 * (a - addr)) 8 else mem a := by
  induction size with
  | zero =>
    intro addr value a
    rw [ite_eq_right (by omega)]
    rfl
  | succ size ih =>
    intro addr value a
    change (if a = addr then _ else writeBytes mem (addr + 1) size _ a) = _
    by_cases same : a = addr
    · subst same
      rw [ite_eq_left rfl, ite_eq_left (by omega)]
      apply BitVec.eq_of_getLsbD_eq
      intro index bound
      simp [getLsbD_rec, bound]
    · rw [ite_eq_right same, ih]
      by_cases inside : addr + 1 ≤ a ∧ a < addr + 1 + size
      · rw [ite_eq_left inside, ite_eq_left (by omega)]
        apply BitVec.eq_of_getLsbD_eq
        intro index bound
        have below : 8 * (a - (addr + 1)) + index < 8 * size := by omega
        have shifted : 8 + (8 * (a - (addr + 1)) + index) = 8 * (a - addr) + index := by omega
        simp [getLsbD_rec, bound, below, shifted]
      · rw [ite_eq_right inside, ite_eq_right (by omega)]

/-- The byte map after lean-sail inserts consecutive bytes. -/
theorem get?_foldl_insert (bytes : Nat → BitVec 8) (addr : Nat) (size : Nat) :
    ∀ (map : Std.ExtHashMap Nat (BitVec 8)) (a : Nat),
      ((List.ofFn fun index : Fin size => (addr + index.val, bytes index.val)).foldl
          (fun map entry => map.insert entry.1 entry.2) map).get? a =
        if addr ≤ a ∧ a < addr + size then some (bytes (a - addr)) else map.get? a := by
  induction size with
  | zero =>
    intro map a
    rw [ite_eq_right (by omega)]
    rfl
  | succ size ih =>
    intro map a
    rw [List.ofFn_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert] at ih ⊢
    simp only [Fin.val_last, Fin.val_castSucc, ih]
    by_cases last : addr + size = a
    · subst last
      simp
    · have different : (addr + size == a) = false := by simpa using last
      rw [different]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases inside : addr ≤ a ∧ a < addr + size
      · rw [ite_eq_left inside, ite_eq_left (by omega)]
      · rw [ite_eq_right inside, ite_eq_right (by omega)]

/-- A loop of single-byte inserts inserts every byte in order. -/
theorem forM_insert (write : Nat × BitVec 8 → ArchSemSeqM exception PUnit)
    (writes : ∀ a v (sequential : SequentialSailState),
      write (a, v) sequential = .ok () { sequential with mem := sequential.mem.insert a v })
    (entries : List (Nat × BitVec 8)) :
    ∀ sequential : SequentialSailState, (List.forM entries write) sequential =
      .ok () { sequential with mem := entries.foldl (fun map entry => map.insert entry.1 entry.2) sequential.mem } := by
  induction entries with
  | nil => intro sequential; rfl
  | cons entry rest ih =>
    intro sequential
    obtain ⟨a, v⟩ := entry
    change (EStateM.bind (write (a, v)) fun _ => List.forM rest write) sequential = _
    simp only [EStateM.bind, writes]
    exact ih _

/-- lean-sail's multi-byte write inserts each byte of the value in order. -/
theorem sequential_writeBytes {size : Nat} (addr : Nat) (value : BitVec (8 * size))
    (sequential : SequentialSailState) :
    (Sail.ArchSem.writeBytes (ue := exception) addr value) sequential =
      .ok () { sequential with
        mem := (List.ofFn fun index : Fin size => (addr + index.val, value.extractLsb' (8 * index.val) 8)).foldl
          (fun map entry => map.insert entry.1 entry.2) sequential.mem } := by
  unfold Sail.ArchSem.writeBytes
  exact forM_insert _ (fun _ _ _ => rfl) _ sequential

/-- Writes keep the agreement. -/
theorem write_agrees {state : SailState} {sequential : SequentialSailState}
    (agrees : SequentialAgrees state sequential) {size : Nat} (addr : Nat) (value : BitVec (8 * size)) :
    SequentialAgrees { state with mem := writeBytes state.mem addr size value }
      { sequential with
        mem := (List.ofFn fun index : Fin size => (addr + index.val, value.extractLsb' (8 * index.val) 8)).foldl
          (fun map entry => map.insert entry.1 entry.2) sequential.mem } := by
  refine ⟨agrees.regs, ?_, agrees.cycles⟩
  intro a reach
  change _ = some (writeBytes state.mem addr size value a)
  rw [writeBytes_apply, get?_foldl_insert (fun index => value.extractLsb' (8 * index) 8)]
  by_cases inside : addr ≤ a ∧ a < addr + size
  · rw [ite_eq_left inside, ite_eq_left inside]
  · rw [ite_eq_right inside, ite_eq_right inside]
    exact agrees.mem a reach

/-- `readBytes` reads only the bytes of its range. -/
theorem readBytes_congr (mem mem' : Nat → BitVec 8) (size : Nat) :
    ∀ addr : Nat, (∀ index, index < size → mem (addr + index) = mem' (addr + index)) →
      readBytes mem addr size = readBytes mem' addr size := by
  induction size with
  | zero => intro addr _; rfl
  | succ size ih =>
    intro addr same
    have first : mem addr = mem' addr := same 0 (by omega)
    have rest := ih (addr + 1) fun index bound => by
      have shifted := same (index + 1) (by omega)
      rwa [show addr + (index + 1) = addr + 1 + index by omega] at shifted
    simp only [Airbender.Reference.RiscV.Sail.Configuration.readBytes, first, rest]

/-- lean-sail's multi-byte read returns the `runSail` bytes when its map holds every byte of the range. -/
theorem sequential_readBytes (mem : Nat → BitVec 8) {sequential : SequentialSailState} (size : Nat) :
    ∀ addr : Nat, (∀ index, index < size → sequential.mem.get? (addr + index) = some (mem (addr + index))) →
      (Sail.ArchSem.readBytes (ue := exception) size addr) sequential = .ok (readBytes mem addr size) sequential := by
  induction size with
  | zero =>
    intro addr _
    change EStateM.Result.ok default sequential = _
    congr 1
  | succ size ih =>
    intro addr present
    have first : sequential.mem.get? addr = some (mem addr) := by simpa using present 0 (by omega)
    cases size with
    | zero =>
      change Sail.ArchSem.readBytes (ue := exception) 1 addr sequential = _
      simp only [Sail.ArchSem.readBytes, Sail.ArchSem.readByte, bind, EStateM.bind, get, getThe,
        MonadStateOf.get, EStateM.get, first, pure, EStateM.pure]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro index bound
      rw [Airbender.Reference.RiscV.Sail.Configuration.readBytes]
      simp only [BitVec.append_eq]
      simp only [BitVec.getLsbD_append]
      simp [bound]
    | succ size =>
      have rest := ih (addr + 1) fun index bound => by
        have shifted := present (index + 1) (by omega)
        rwa [show addr + (index + 1) = addr + 1 + index by omega] at shifted
      simp only [Sail.ArchSem.readBytes, Sail.ArchSem.readByte, bind, EStateM.bind, get, getThe,
        MonadStateOf.get, EStateM.get, first, pure, EStateM.pure, rest]
      rfl

end Proven.Interpreter
