module
public import Proven.NonVacuous.KeccakSplitSpan.Steps
public import Proven.NonVacuous.KeccakSplitSpan.Chi.Row

@[expose] public section

/-! A chi call's honest row (`RowFacts`): its twelve ports read their keys' tokens (the grouped read clocks are the
    clocks of their groups' first ports, `group`) and write canonical words: x10 the next control word, x11 the
    pointer, each lane its chi limbs. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Chi
open Arithmetic Trace Keccak.Split Keccak.Split.SetupProofs

local notation "P" => babyBearModulus

variable {mem : Memory} {k : Nat}

theorem row_eq (kind : kindAt k = .chi5) :
    mem.row k = ⟨.chi5, Chi.assignment (mem.input k)⟩ := by
  simp only [Memory.row, KeccakSplitSpan.assignment, Memory.input, kind]

theorem out_lt (x : RowInput) (i m : Nat) : out x i m < 65536 := by
  have nibble (n : Nat) : chiNib x i n < 16 :=
    Nat.xor_lt_two_pow (n := 4) (nib_lt _ _) (Nat.lt_of_le_of_lt Nat.and_le_right (nib_lt _ _))
  have n0 := nibble (4 * m)
  have n1 := nibble (4 * m + 1)
  have n2 := nibble (4 * m + 2)
  have n3 := nibble (4 * m + 3)
  unfold out
  omega

theorem row_facts (inv : Inv mem k) (call : k < 361) (kind : kindAt k = .chi5)
    (group : ∀ j,
        j < portCount k → (mem (portKey k j)).time.1.val =
        (mem (portKey k (if j < 2 then 0 else 2 + 2 * ((j - 2) / 2)))).time.1.val) :
    RowFacts mem k := by
  have count : portCount k = 12 := by rw [portCount, kind]; rfl
  have valid := valid_of_inv inv call
  have inside (j : Nat) (h : j < 12 := by decide) : portKey k j < 62 := portKey_lt (by rw [count]; exact h)
  have slot (j l h : Nat) (port : j < 12 := by decide) (shape : 2 + 2 * slotNat k l + h = portKey k j := by rfl) :
      slotNat k l < 30 := by
    have := inside j port
    omega
  have lo : Chi.assignment (mem.input k) 12 = ((0 : Nat) : ZMod P) := by
    show (((mem 1).word.lo : Nat) : ZMod P) = _
    rw [inv.pointer]
  have hi : Chi.assignment (mem.input k) 13 = ((64 : Nat) : ZMod P) := by
    show (((mem 1).word.hi : Nat) : ZMod P) = _
    rw [inv.pointer]
  set r : Native.Row P := ⟨.chi5, Chi.assignment (mem.input k)⟩ with hr
  have read (j : Nat) (h : j < 12) : readToken r.assignment (r.ports[j]'(by change j < 12; exact h)) =
      mem (portKey k j) := by
    interval_cases j
    · exact register_read (c0 := 175) (c1 := 176) (r0 := 3) (r1 := 4) rfl rfl
        (by show _ = (mem 0).address; rw [inv.address 0 (by decide)]; rfl) rfl rfl
        (by show ((controlAt k : Nat) : ZMod P) = (((mem 0).word.lo : Nat) : ZMod P); rw [inv.control call])
        (by show ((0 : Nat) : ZMod P) = (((mem 0).word.hi : Nat) : ZMod P); rw [inv.control call])
        (inv.high 0 (by decide)) (inv.words 0 (by decide))
    · exact register_read (c0 := 175) (c1 := 176) (r0 := 12) (r1 := 13) rfl rfl
        (by show _ = (mem 1).address; rw [inv.address 1 (by decide)]; rfl)
            (congrArg (fun v : Nat => (v : ZMod P)) (group 1 (by rw [count]; decide))).symm rfl rfl rfl
            (inv.high 1 (by decide)) (inv.words 1 (by decide))
    · exact lane_read (c0 := 177) (c1 := 178) (r0 := 14) (r1 := 15) (b0 := 12) (b1 := 13) (o := 7)
        (s := slotNat k 0) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 2)) (inv.high _ (inside 2)) (inv.words _ (inside 2)) (slot 2 0 0) (by decide)
    · exact lane_read (c0 := 177) (c1 := 178) (r0 := 18) (r1 := 19) (b0 := 12) (b1 := 13) (o := 7)
        (s := slotNat k 0) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 3 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 3)) (inv.high _ (inside 3)) (inv.words _ (inside 3)) (slot 3 0 1) (by decide)
    · exact lane_read (c0 := 179) (c1 := 180) (r0 := 22) (r1 := 23) (b0 := 12) (b1 := 13) (o := 8)
        (s := slotNat k 1) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 4)) (inv.high _ (inside 4)) (inv.words _ (inside 4)) (slot 4 1 0) (by decide)
    · exact lane_read (c0 := 179) (c1 := 180) (r0 := 26) (r1 := 27) (b0 := 12) (b1 := 13) (o := 8)
        (s := slotNat k 1) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 5 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 5)) (inv.high _ (inside 5)) (inv.words _ (inside 5)) (slot 5 1 1) (by decide)
    · exact lane_read (c0 := 181) (c1 := 182) (r0 := 30) (r1 := 31) (b0 := 12) (b1 := 13) (o := 9)
        (s := slotNat k 2) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 6)) (inv.high _ (inside 6)) (inv.words _ (inside 6)) (slot 6 2 0) (by decide)
    · exact lane_read (c0 := 181) (c1 := 182) (r0 := 34) (r1 := 35) (b0 := 12) (b1 := 13) (o := 9)
        (s := slotNat k 2) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 7 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 7)) (inv.high _ (inside 7)) (inv.words _ (inside 7)) (slot 7 2 1) (by decide)
    · exact lane_read (c0 := 183) (c1 := 184) (r0 := 38) (r1 := 39) (b0 := 12) (b1 := 13) (o := 10)
        (s := slotNat k 3) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 8)) (inv.high _ (inside 8)) (inv.words _ (inside 8)) (slot 8 3 0) (by decide)
    · exact lane_read (c0 := 183) (c1 := 184) (r0 := 42) (r1 := 43) (b0 := 12) (b1 := 13) (o := 10)
        (s := slotNat k 3) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 9 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 9)) (inv.high _ (inside 9)) (inv.words _ (inside 9)) (slot 9 3 1) (by decide)
    · exact lane_read (c0 := 185) (c1 := 186) (r0 := 46) (r1 := 47) (b0 := 12) (b1 := 13) (o := 11)
        (s := slotNat k 4) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 10)) (inv.high _ (inside 10)) (inv.words _ (inside 10)) (slot 10 4 0) (by decide)
    · exact lane_read (c0 := 185) (c1 := 186) (r0 := 50) (r1 := 51) (b0 := 12) (b1 := 13) (o := 11)
        (s := slotNat k 4) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 11 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 11)) (inv.high _ (inside 11)) (inv.words _ (inside 11)) (slot 11 4 1) (by decide)
  refine RowFacts.of_row (row_eq kind) (by rw [count]; rfl) (fun j h => read j (count ▸ h))
    (fun j h => by rw [count] at h; interval_cases j <;> rfl) rfl rfl rfl (fun j h => ?_)
  rw [count] at h
  interval_cases j
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[0]'(by show 0 < 12; decide))) rfl
      (a := bump (controlAt k)) (b := 0) (RowProofs.bump_small (SetupProofs.controlAt_lt call)) (by decide)
    rw [word]
    refine ⟨⟨?_, ?_⟩, fun _ => rfl, by omega⟩
    · simp only [limbBase]
      exact RowProofs.bump_small (SetupProofs.controlAt_lt call)
    · simp only [limbBase]
      exact by decide
  · have same : (r.writeToken (r.ports[1]'(by show 1 < 12; decide))).word = (mem 1).word := by
      rw [readonly_word rfl, read 1 (by decide)]
      rfl
    rw [same, inv.pointer]
    exact ⟨⟨by decide, by decide⟩, by omega, fun _ => rfl⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[2]'(by show 2 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 0 0) (b := Chi.out (mem.input k) 0 1) (Chi.out_lt _ 0 0) (Chi.out_lt _ 0 1)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 0 0, by simp only [limbBase]; exact Chi.out_lt _ 0 1⟩,
        by omega, by omega⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[3]'(by show 3 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 0 2) (b := Chi.out (mem.input k) 0 3) (Chi.out_lt _ 0 2) (Chi.out_lt _ 0 3)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 0 2, by simp only [limbBase]; exact Chi.out_lt _ 0 3⟩,
        by omega, by omega⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[4]'(by show 4 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 1 0) (b := Chi.out (mem.input k) 1 1) (Chi.out_lt _ 1 0) (Chi.out_lt _ 1 1)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 1 0, by simp only [limbBase]; exact Chi.out_lt _ 1 1⟩,
        by omega, by omega⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[5]'(by show 5 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 1 2) (b := Chi.out (mem.input k) 1 3) (Chi.out_lt _ 1 2) (Chi.out_lt _ 1 3)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 1 2, by simp only [limbBase]; exact Chi.out_lt _ 1 3⟩,
        by omega, by omega⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[6]'(by show 6 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 2 0) (b := Chi.out (mem.input k) 2 1) (Chi.out_lt _ 2 0) (Chi.out_lt _ 2 1)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 2 0, by simp only [limbBase]; exact Chi.out_lt _ 2 1⟩,
        by omega, by omega⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[7]'(by show 7 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 2 2) (b := Chi.out (mem.input k) 2 3) (Chi.out_lt _ 2 2) (Chi.out_lt _ 2 3)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 2 2, by simp only [limbBase]; exact Chi.out_lt _ 2 3⟩,
        by omega, by omega⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[8]'(by show 8 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 3 0) (b := Chi.out (mem.input k) 3 1) (Chi.out_lt _ 3 0) (Chi.out_lt _ 3 1)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 3 0, by simp only [limbBase]; exact Chi.out_lt _ 3 1⟩,
        by omega, by omega⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[9]'(by show 9 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 3 2) (b := Chi.out (mem.input k) 3 3) (Chi.out_lt _ 3 2) (Chi.out_lt _ 3 3)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 3 2, by simp only [limbBase]; exact Chi.out_lt _ 3 3⟩,
        by omega, by omega⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[10]'(by show 10 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 4 0) (b := Chi.out (mem.input k) 4 1) (Chi.out_lt _ 4 0) (Chi.out_lt _ 4 1)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 4 0, by simp only [limbBase]; exact Chi.out_lt _ 4 1⟩,
        by omega, by omega⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[11]'(by show 11 < 12; decide))) rfl
      (a := Chi.out (mem.input k) 4 2) (b := Chi.out (mem.input k) 4 3) (Chi.out_lt _ 4 2) (Chi.out_lt _ 4 3)
    rw [word]
    exact ⟨⟨by simp only [limbBase]; exact Chi.out_lt _ 4 2, by simp only [limbBase]; exact Chi.out_lt _ 4 3⟩,
        by omega, by omega⟩

end Airbender.NonVacuous.KeccakSplitSpan.Chi
