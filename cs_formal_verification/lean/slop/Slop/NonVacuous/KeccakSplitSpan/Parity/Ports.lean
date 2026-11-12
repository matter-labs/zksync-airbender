module
public import Slop.NonVacuous.KeccakSplitSpan.Steps
public import Slop.NonVacuous.KeccakSplitSpan.Parity.Lookups

@[expose] public section

/-! A column-parity call's honest row (`RowFacts`): its fourteen ports read their keys' tokens and write canonical
    words: x10 the next control word, x11 the pointer, the first lane its iota limbs, the parity slot the parity. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Parity
open Arithmetic Trace Keccak.Split Keccak.Split.SetupProofs

local notation "P" => babyBearModulus

variable {mem : Memory} {k : Nat}

theorem row_eq (kind : kindAt k = .columnParity) :
    mem.row k = ⟨.columnParity, Parity.assignment (mem.input k)⟩ := by
  simp only [Memory.row, KeccakSplitSpan.assignment, Memory.input, kind]

theorem row_facts (inv : Inv mem k) (call : k < 361) (kind : kindAt k = .columnParity) :
    RowFacts mem k := by
  have count : portCount k = 14 := by rw [portCount, kind]; rfl
  have valid := valid_of_inv inv call
  have inside (j : Nat) (h : j < 14 := by decide) : portKey k j < 62 := portKey_lt (by rw [count]; exact h)
  have slot (j l h : Nat) (port : j < 14 := by decide) (shape : 2 + 2 * slotNat k l + h = portKey k j := by rfl) :
      slotNat k l < 30 := by
    have := inside j port
    omega
  have lo : Parity.assignment (mem.input k) 13 = ((0 : Nat) : ZMod P) := by
    show (((mem 1).word.lo : Nat) : ZMod P) = _
    rw [inv.pointer]
  have hi : Parity.assignment (mem.input k) 14 = ((64 : Nat) : ZMod P) := by
    show (((mem 1).word.hi : Nat) : ZMod P) = _
    rw [inv.pointer]
  set r : Native.Row P := ⟨.columnParity, Parity.assignment (mem.input k)⟩ with hr
  have read (j : Nat) (h : j < 14) : readToken r.assignment (r.ports[j]'(by change j < 14; exact h)) =
      mem (portKey k j) := by
    interval_cases j
    · exact register_read (c0 := 123) (c1 := 124) (r0 := 3) (r1 := 4) rfl rfl
        (by show _ = (mem 0).address; rw [inv.address 0 (by decide)]; rfl) rfl rfl
        (by show ((controlAt k : Nat) : ZMod P) = (((mem 0).word.lo : Nat) : ZMod P); rw [inv.control call])
        (by show ((0 : Nat) : ZMod P) = (((mem 0).word.hi : Nat) : ZMod P); rw [inv.control call])
        (inv.high 0 (by decide)) (inv.words 0 (by decide))
    · exact register_read (c0 := 126) (c1 := 127) (r0 := 13) (r1 := 14) rfl rfl
        (by show _ = (mem 1).address; rw [inv.address 1 (by decide)]; rfl) rfl rfl rfl rfl (inv.high 1 (by decide))
            (inv.words 1 (by decide))
    · exact lane_read (c0 := 129) (c1 := 130) (r0 := 15) (r1 := 16) (b0 := 13) (b1 := 14) (o := 7)
        (s := slotNat k 0) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 2)) (inv.high _ (inside 2)) (inv.words _ (inside 2)) (slot 2 0 0) (by decide)
    · exact lane_read (c0 := 132) (c1 := 133) (r0 := 19) (r1 := 20) (b0 := 13) (b1 := 14) (o := 7)
        (s := slotNat k 0) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 3)) (inv.high _ (inside 3)) (inv.words _ (inside 3)) (slot 3 0 1) (by decide)
    · exact lane_read (c0 := 135) (c1 := 136) (r0 := 23) (r1 := 24) (b0 := 13) (b1 := 14) (o := 8)
        (s := slotNat k 1) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 4)) (inv.high _ (inside 4)) (inv.words _ (inside 4)) (slot 4 1 0) (by decide)
    · exact lane_read (c0 := 138) (c1 := 139) (r0 := 25) (r1 := 26) (b0 := 13) (b1 := 14) (o := 8)
        (s := slotNat k 1) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 5)) (inv.high _ (inside 5)) (inv.words _ (inside 5)) (slot 5 1 1) (by decide)
    · exact lane_read (c0 := 141) (c1 := 142) (r0 := 27) (r1 := 28) (b0 := 13) (b1 := 14) (o := 9)
        (s := slotNat k 2) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 6)) (inv.high _ (inside 6)) (inv.words _ (inside 6)) (slot 6 2 0) (by decide)
    · exact lane_read (c0 := 144) (c1 := 145) (r0 := 29) (r1 := 30) (b0 := 13) (b1 := 14) (o := 9)
        (s := slotNat k 2) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 7)) (inv.high _ (inside 7)) (inv.words _ (inside 7)) (slot 7 2 1) (by decide)
    · exact lane_read (c0 := 147) (c1 := 148) (r0 := 31) (r1 := 32) (b0 := 13) (b1 := 14) (o := 10)
        (s := slotNat k 3) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 8)) (inv.high _ (inside 8)) (inv.words _ (inside 8)) (slot 8 3 0) (by decide)
    · exact lane_read (c0 := 150) (c1 := 151) (r0 := 33) (r1 := 34) (b0 := 13) (b1 := 14) (o := 10)
        (s := slotNat k 3) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 9)) (inv.high _ (inside 9)) (inv.words _ (inside 9)) (slot 9 3 1) (by decide)
    · exact lane_read (c0 := 153) (c1 := 154) (r0 := 35) (r1 := 36) (b0 := 13) (b1 := 14) (o := 11)
        (s := slotNat k 4) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 10)) (inv.high _ (inside 10)) (inv.words _ (inside 10)) (slot 10 4 0) (by decide)
    · exact lane_read (c0 := 156) (c1 := 157) (r0 := 37) (r1 := 38) (b0 := 13) (b1 := 14) (o := 11)
        (s := slotNat k 4) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 11)) (inv.high _ (inside 11)) (inv.words _ (inside 11)) (slot 11 4 1) (by decide)
    · exact lane_read (c0 := 159) (c1 := 160) (r0 := 39) (r1 := 40) (b0 := 13) (b1 := 14) (o := 12)
        (s := slotNat k 5) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 12)) (inv.high _ (inside 12)) (inv.words _ (inside 12)) (slot 12 5 0) (by decide)
    · exact lane_read (c0 := 162) (c1 := 163) (r0 := 43) (r1 := 44) (b0 := 13) (b1 := 14) (o := 12)
        (s := slotNat k 5) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 13)) (inv.high _ (inside 13)) (inv.words _ (inside 13)) (slot 13 5 1) (by decide)
  refine RowFacts.of_row (row_eq kind) (by rw [count]; rfl) (fun j h => read j (count ▸ h))
    (fun j h => by rw [count] at h; interval_cases j <;> rfl) rfl rfl rfl (fun j h => ?_)
  rw [count] at h
  interval_cases j
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[0]'(by show 0 < 14; decide))) rfl
      (a := bump (controlAt k)) (b := 0) (RowProofs.bump_small (SetupProofs.controlAt_lt call)) (by decide)
    rw [word]
    refine ⟨⟨?_, ?_⟩, fun _ => rfl, by omega⟩
    · simp only [limbBase]
      exact RowProofs.bump_small (SetupProofs.controlAt_lt call)
    · simp only [limbBase]
      exact by decide
  · have same : (r.writeToken (r.ports[1]'(by show 1 < 14; decide))).word = (mem 1).word := by
      rw [readonly_word rfl, read 1 (by decide)]
      rfl
    rw [same, inv.pointer]
    exact ⟨⟨by decide, by decide⟩, by omega, fun _ => rfl⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[2]'(by show 2 < 14; decide))) rfl
      (a := Parity.out (mem.input k) 0) (b := Parity.out (mem.input k) 1) (Parity.out_lt valid kind 0)
          (Parity.out_lt valid kind 1)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact Parity.out_lt valid kind 0
    · simp only [limbBase]
      exact Parity.out_lt valid kind 1
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[3]'(by show 3 < 14; decide))) rfl
      (a := Parity.out (mem.input k) 2) (b := Parity.out (mem.input k) 3) (Parity.out_lt valid kind 2)
          (Parity.out_lt valid kind 3)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact Parity.out_lt valid kind 2
    · simp only [limbBase]
      exact Parity.out_lt valid kind 3
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 4 (by decide)]
    exact inv.words _ (inside 4)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 5 (by decide)]
    exact inv.words _ (inside 5)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 6 (by decide)]
    exact inv.words _ (inside 6)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 7 (by decide)]
    exact inv.words _ (inside 7)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 8 (by decide)]
    exact inv.words _ (inside 8)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 9 (by decide)]
    exact inv.words _ (inside 9)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 10 (by decide)]
    exact inv.words _ (inside 10)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 11 (by decide)]
    exact inv.words _ (inside 11)
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[12]'(by show 12 < 14; decide))) rfl
      (a := Parity.parity (mem.input k) 0) (b := Parity.parity (mem.input k) 1) (Parity.parity_lt _ 0)
          (Parity.parity_lt _ 1)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact Parity.parity_lt _ 0
    · simp only [limbBase]
      exact Parity.parity_lt _ 1
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[13]'(by show 13 < 14; decide))) rfl
      (a := Parity.parity (mem.input k) 2) (b := Parity.parity (mem.input k) 3) (Parity.parity_lt _ 2)
          (Parity.parity_lt _ 3)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact Parity.parity_lt _ 2
    · simp only [limbBase]
      exact Parity.parity_lt _ 3

end Airbender.NonVacuous.KeccakSplitSpan.Parity
