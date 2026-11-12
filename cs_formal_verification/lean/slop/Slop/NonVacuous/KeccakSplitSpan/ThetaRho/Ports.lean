module
public import Slop.NonVacuous.KeccakSplitSpan.Steps
public import Slop.NonVacuous.KeccakSplitSpan.ThetaRho.Values

@[expose] public section

/-! A theta+rho call's honest row (`RowFacts`): its sixteen ports read their keys' tokens (the grouped read clocks are
    the clocks of their groups' first ports, `group`) and write canonical words: x10 the next control word, x11 the
    pointer, each lane its rotated limbs. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Trace Keccak.Split Keccak.Split.SetupProofs

local notation "P" => babyBearModulus

variable {mem : Memory} {k : Nat}

theorem row_eq (kind : kindAt k = .thetaRho) :
    mem.row k = ⟨.thetaRho, ThetaRho.assignment (mem.input k)⟩ := by
  simp only [Memory.row, KeccakSplitSpan.assignment, Memory.input, kind]

theorem row_facts (inv : Inv mem k) (call : k < 361) (kind : kindAt k = .thetaRho)
    (group : ∀ j,
        j < portCount k → (mem (portKey k j)).time.1.val =
        (mem (portKey k (if j < 2 then 0 else if j < 12 then 2 else if j < 14 then 12 else 14))).time.1.val) :
    RowFacts mem k := by
  have count : portCount k = 16 := by rw [portCount, kind]; rfl
  have valid := valid_of_inv inv call
  have inside (j : Nat) (h : j < 16 := by decide) : portKey k j < 62 := portKey_lt (by rw [count]; exact h)
  have slot (j l h : Nat) (port : j < 16 := by decide) (shape : 2 + 2 * slotNat k l + h = portKey k j := by rfl) :
      slotNat k l < 30 := by
    have := inside j port
    omega
  have lo : ThetaRho.assignment (mem.input k) 14 = ((0 : Nat) : ZMod P) := by
    show (((mem 1).word.lo : Nat) : ZMod P) = _
    rw [inv.pointer]
  have hi : ThetaRho.assignment (mem.input k) 15 = ((64 : Nat) : ZMod P) := by
    show (((mem 1).word.hi : Nat) : ZMod P) = _
    rw [inv.pointer]
  set r : Native.Row P := ⟨.thetaRho, ThetaRho.assignment (mem.input k)⟩ with hr
  have read (j : Nat) (h : j < 16) : readToken r.assignment (r.ports[j]'(by change j < 16; exact h)) =
      mem (portKey k j) := by
    interval_cases j
    · exact register_read (c0 := 189) (c1 := 190) (r0 := 3) (r1 := 4) rfl rfl
        (by show _ = (mem 0).address; rw [inv.address 0 (by decide)]; rfl) rfl rfl
        (by show ((controlAt k : Nat) : ZMod P) = (((mem 0).word.lo : Nat) : ZMod P); rw [inv.control call])
        (by show ((0 : Nat) : ZMod P) = (((mem 0).word.hi : Nat) : ZMod P); rw [inv.control call])
        (inv.high 0 (by decide)) (inv.words 0 (by decide))
    · exact register_read (c0 := 189) (c1 := 190) (r0 := 14) (r1 := 15) rfl rfl
        (by show _ = (mem 1).address; rw [inv.address 1 (by decide)]; rfl)
            (congrArg (fun v : Nat => (v : ZMod P)) (group 1 (by rw [count]; decide))).symm rfl rfl rfl
            (inv.high 1 (by decide)) (inv.words 1 (by decide))
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 16) (r1 := 17) (b0 := 14) (b1 := 15) (o := 7)
        (s := slotNat k 0) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 2)) (inv.high _ (inside 2)) (inv.words _ (inside 2)) (slot 2 0 0) (by decide)
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 20) (r1 := 21) (b0 := 14) (b1 := 15) (o := 7)
        (s := slotNat k 0) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 3 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 3)) (inv.high _ (inside 3)) (inv.words _ (inside 3)) (slot 3 0 1) (by decide)
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 24) (r1 := 25) (b0 := 14) (b1 := 15) (o := 8)
        (s := slotNat k 1) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 4 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 4)) (inv.high _ (inside 4)) (inv.words _ (inside 4)) (slot 4 1 0) (by decide)
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 28) (r1 := 29) (b0 := 14) (b1 := 15) (o := 8)
        (s := slotNat k 1) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 5 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 5)) (inv.high _ (inside 5)) (inv.words _ (inside 5)) (slot 5 1 1) (by decide)
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 32) (r1 := 33) (b0 := 14) (b1 := 15) (o := 9)
        (s := slotNat k 2) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 6 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 6)) (inv.high _ (inside 6)) (inv.words _ (inside 6)) (slot 6 2 0) (by decide)
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 36) (r1 := 37) (b0 := 14) (b1 := 15) (o := 9)
        (s := slotNat k 2) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 7 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 7)) (inv.high _ (inside 7)) (inv.words _ (inside 7)) (slot 7 2 1) (by decide)
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 40) (r1 := 41) (b0 := 14) (b1 := 15) (o := 10)
        (s := slotNat k 3) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 8 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 8)) (inv.high _ (inside 8)) (inv.words _ (inside 8)) (slot 8 3 0) (by decide)
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 44) (r1 := 45) (b0 := 14) (b1 := 15) (o := 10)
        (s := slotNat k 3) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 9 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 9)) (inv.high _ (inside 9)) (inv.words _ (inside 9)) (slot 9 3 1) (by decide)
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 48) (r1 := 49) (b0 := 14) (b1 := 15) (o := 11)
        (s := slotNat k 4) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 10 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 10)) (inv.high _ (inside 10)) (inv.words _ (inside 10)) (slot 10 4 0) (by decide)
    · exact lane_read (c0 := 191) (c1 := 192) (r0 := 52) (r1 := 53) (b0 := 14) (b1 := 15) (o := 11)
        (s := slotNat k 4) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 11 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 11)) (inv.high _ (inside 11)) (inv.words _ (inside 11)) (slot 11 4 1) (by decide)
    · exact lane_read (c0 := 193) (c1 := 194) (r0 := 56) (r1 := 57) (b0 := 14) (b1 := 15) (o := 12)
        (s := slotNat k 5) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 12)) (inv.high _ (inside 12)) (inv.words _ (inside 12)) (slot 12 5 0) (by decide)
    · exact lane_read (c0 := 193) (c1 := 194) (r0 := 58) (r1 := 59) (b0 := 14) (b1 := 15) (o := 12)
        (s := slotNat k 5) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 13 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 13)) (inv.high _ (inside 13)) (inv.words _ (inside 13)) (slot 13 5 1) (by decide)
    · exact lane_read (c0 := 195) (c1 := 196) (r0 := 60) (r1 := 61) (b0 := 14) (b1 := 15) (o := 13)
        (s := slotNat k 6) (h := 0) rfl rfl rfl rfl rfl rfl rfl lo hi rfl rfl rfl rfl rfl
        (inv.address _ (inside 14)) (inv.high _ (inside 14)) (inv.words _ (inside 14)) (slot 14 6 0) (by decide)
    · exact lane_read (c0 := 195) (c1 := 196) (r0 := 62) (r1 := 63) (b0 := 14) (b1 := 15) (o := 13)
        (s := slotNat k 6) (h := 1) rfl rfl rfl rfl rfl rfl rfl lo hi rfl
            (congrArg (fun v : Nat => (v : ZMod P)) (group 15 (by rw [count]; decide))).symm rfl rfl rfl
        (inv.address _ (inside 15)) (inv.high _ (inside 15)) (inv.words _ (inside 15)) (slot 15 6 1) (by decide)
  refine RowFacts.of_row (row_eq kind) (by rw [count]; rfl) (fun j h => read j (count ▸ h))
    (fun j h => by rw [count] at h; interval_cases j <;> rfl) rfl rfl rfl (fun j h => ?_)
  rw [count] at h
  interval_cases j
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[0]'(by show 0 < 16; decide))) rfl
      (a := bump (controlAt k)) (b := 0) (RowProofs.bump_small (SetupProofs.controlAt_lt call)) (by decide)
    rw [word]
    refine ⟨⟨?_, ?_⟩, fun _ => rfl, by omega⟩
    · simp only [limbBase]
      exact RowProofs.bump_small (SetupProofs.controlAt_lt call)
    · simp only [limbBase]
      exact by decide
  · have same : (r.writeToken (r.ports[1]'(by show 1 < 16; decide))).word = (mem 1).word := by
      rw [readonly_word rfl, read 1 (by decide)]
      rfl
    rw [same, inv.pointer]
    exact ⟨⟨by decide, by decide⟩, by omega, fun _ => rfl⟩
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[2]'(by show 2 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 0 0) (b := ThetaRho.out (mem.input k) 0 1)
          (ThetaRho.out_lt valid kind (by decide) 0) (ThetaRho.out_lt valid kind (by decide) 1)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 0
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 1
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[3]'(by show 3 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 0 2) (b := ThetaRho.out (mem.input k) 0 3)
          (ThetaRho.out_lt valid kind (by decide) 2) (ThetaRho.out_lt valid kind (by decide) 3)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 2
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 3
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[4]'(by show 4 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 1 0) (b := ThetaRho.out (mem.input k) 1 1)
          (ThetaRho.out_lt valid kind (by decide) 0) (ThetaRho.out_lt valid kind (by decide) 1)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 0
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 1
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[5]'(by show 5 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 1 2) (b := ThetaRho.out (mem.input k) 1 3)
          (ThetaRho.out_lt valid kind (by decide) 2) (ThetaRho.out_lt valid kind (by decide) 3)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 2
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 3
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[6]'(by show 6 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 2 0) (b := ThetaRho.out (mem.input k) 2 1)
          (ThetaRho.out_lt valid kind (by decide) 0) (ThetaRho.out_lt valid kind (by decide) 1)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 0
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 1
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[7]'(by show 7 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 2 2) (b := ThetaRho.out (mem.input k) 2 3)
          (ThetaRho.out_lt valid kind (by decide) 2) (ThetaRho.out_lt valid kind (by decide) 3)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 2
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 3
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[8]'(by show 8 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 3 0) (b := ThetaRho.out (mem.input k) 3 1)
          (ThetaRho.out_lt valid kind (by decide) 0) (ThetaRho.out_lt valid kind (by decide) 1)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 0
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 1
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[9]'(by show 9 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 3 2) (b := ThetaRho.out (mem.input k) 3 3)
          (ThetaRho.out_lt valid kind (by decide) 2) (ThetaRho.out_lt valid kind (by decide) 3)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 2
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 3
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[10]'(by show 10 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 4 0) (b := ThetaRho.out (mem.input k) 4 1)
          (ThetaRho.out_lt valid kind (by decide) 0) (ThetaRho.out_lt valid kind (by decide) 1)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 0
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 1
  · have word := token_word (by decide) (tok := r.writeToken (r.ports[11]'(by show 11 < 16; decide))) rfl
      (a := ThetaRho.out (mem.input k) 4 2) (b := ThetaRho.out (mem.input k) 4 3)
          (ThetaRho.out_lt valid kind (by decide) 2) (ThetaRho.out_lt valid kind (by decide) 3)
    rw [word]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 2
    · simp only [limbBase]
      exact ThetaRho.out_lt valid kind (by decide) 3
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 12 (by decide)]
    exact inv.words _ (inside 12)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 13 (by decide)]
    exact inv.words _ (inside 13)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 14 (by decide)]
    exact inv.words _ (inside 14)
  · refine ⟨?_, by omega, by omega⟩
    rw [readonly_word rfl, read 15 (by decide)]
    exact inv.words _ (inside 15)

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
