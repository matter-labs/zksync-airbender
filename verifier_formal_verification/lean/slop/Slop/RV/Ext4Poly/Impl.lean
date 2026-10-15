import Slop.RV.Horner
import Slop.RV.MulAdd.Impl
import Slop.RV.Ext4Poly.PartA
import Slop.RV.Ext4Poly.PartB

/-! `ext4_poly(out, y)` in plain Rust: block A (`new` on `y`), `ext4_horner` over `COEFFS4` (with the plain
`ext4_mul_add`), block B (`to_u32`). -/

namespace RV
open Spec
set_option maxHeartbeats 0

/-- `ext4_poly` (plain) at `A`, with `ext4_horner` at `A - 0x68c` and its `ext4_mul_add` after it. -/
theorem ext4_poly_impl (A : Word) (hA : 0x68c ≤ A.toNat) (hAr : A.toNat + 560 ≤ 4194304) :
    ImplementsAtW A Code.ext4_poly [(A + 4294965620#32, Code.ext4_horner),
      (A + 4294965620#32 + 168#32, Code.ext4_mul_add)] 192 e4polyPre 16 e4polyPost := by
  intro s hentry hcallees hcall hpre
  have hcH := hcallees (A + 4294965620#32, Code.ext4_horner) (.head _)
  have hcM := hcallees (A + 4294965620#32 + 168#32, Code.ext4_mul_add) (.tail _ (.head _))
  dsimp only at hcH hcM
  clear hcallees
  simp only [e4polyPre, argOk, RAM_END] at hpre
  obtain ⟨⟨ho4, hos, hor⟩, ⟨hy4, hys, hyr⟩, hcy, htab, hspT⟩ := hpre
  rw [Call, hentry] at hcall
  obtain ⟨hcode, hal, hrom, hra, hsp16, hspl, hspr⟩ := hcall
  replace hra : (s.getReg 1#5).toNat % 4 = 0 := hra
  replace hsp16 : (s.getReg 2#5).toNat % 16 = 0 := hsp16
  replace hspl : ROM_END + 192 ≤ (s.getReg 2#5).toNat := hspl
  replace hspr : (s.getReg 2#5).toNat ≤ RAM_END := hspr
  have hlen : Code.ext4_poly.length = 140 := by decide +kernel
  have hlenH : Code.ext4_horner.length = 42 := by decide +kernel
  have hlenM : Code.ext4_mul_add.length = 377 := by decide +kernel
  rw [hlen] at hrom
  simp only [ROM_END, RAM_END] at *
  unfold ReturnsW
  -- block A and the `jal`
  obtain ⟨S1, hrun1, hpc1, r1, r2, r10, r11, r12, r13, r9, r18, r19, r20, r22, hrom1, hmem1, hcan1, he1,
    k1, k8, k9, k18, k19, k20, k21⟩ := poly_part_a A s hentry hcode hal (by simp only [ROM_END]; omega) hA hsp16
      (by simp only [ROM_END]; omega) hspT hy4 hys (by simp only [RAM_END]; omega) hcy
  -- `ext4_horner`
  have hH := ext4_horner_impl (A + 4294965620#32) Code.ext4_mul_add [] 80 (ext4_mul_add_impl _)
    (by rw [hlenM]; bv_omega) (by simp)
  have htab1 : CodeMem S1.mem 0x1400190#32 Code.COEFFS4 := fun i hi => by
    rw [read_congr S1.mem s.mem _ 4 (fun j hj => hmem1 _ (by right; rw [coeffs4_length] at hi; bv_omega))]
    exact htab i hi
  have hcH1 := codeAt_of_rom hcH (by rw [hlenH]; simp only [ROM_END]; bv_omega) hrom1
  have hcM1 := codeAt_of_rom hcM (by rw [hlenM]; simp only [ROM_END]; bv_omega) hrom1
  obtain ⟨n2, S2, hrun2, hpc2, hpost2, hcs2, hmem2⟩ := hH S1 hpc1
    (by intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact hcM1)
    ⟨by rw [hpc1]; exact hcH1, by rw [hpc1]; bv_omega, by rw [hpc1, hlenH]; simp only [ROM_END]; bv_omega,
      by show (S1.getReg 1#5).toNat % 4 = 0; rw [r1]; bv_omega,
      by show (S1.getReg 2#5).toNat % 16 = 0; rw [r2]; bv_omega,
      by show ROM_END + (48 + 80) ≤ (S1.getReg 2#5).toNat; rw [r2]; simp only [ROM_END]; bv_omega,
      by show (S1.getReg 2#5).toNat ≤ RAM_END; rw [r2]; simp only [RAM_END]; bv_omega⟩
    (by
      simp only [hornerPre, argOk, RAM_END, r2, r10, r11, r12, r13]
      refine ⟨⟨by bv_omega, by bv_omega, by bv_omega⟩, ⟨by bv_omega, by bv_omega, by bv_omega⟩, hcan1, by decide,
        by bv_omega, by decide, fun i hi => (table4 htab1 i (by simpa using hi)).1⟩)
  replace hmem2 : ∀ a : Word, a.toNat + (48 + 80) < (S1.getReg 2#5).toNat ∨ (S1.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (S1.getReg 10#5).toNat ∨ (S1.getReg 10#5).toNat + 16 ≤ a.toNat → S2.mem a = S1.mem a := hmem2
  replace hpc2 : S2.pc = S1.getReg 1#5 := hpc2
  simp only [hornerPost, r10, r11, r12, r13] at hpost2
  obtain ⟨hcanon2, hval2⟩ := hpost2
  have cs : ∀ i : Reg, calleeSaved i → S2.getReg i = S1.getReg i := hcs2
  have hrom2 : ∀ b : Word, b.toNat < ROM_END → S2.mem b = s.mem b := fun b hb => by
    rw [hmem2 b (by left; rw [r2]; simp only [ROM_END] at hb; bv_omega)
      (by left; rw [r10]; simp only [ROM_END] at hb; bv_omega), hrom1 b hb]
  -- the frame of `ext4_poly` above the callee's, outside `e`: unchanged by `ext4_horner`
  have keep : ∀ k : Word, 36 ≤ k.toNat → k.toNat ≤ 60 →
      read S2.mem (s.getReg 2#5 + 4294967232#32 + k) 4 = read S1.mem (s.getReg 2#5 + 4294967232#32 + k) 4 :=
    fun k h1 h2 => read_congr _ _ _ _ (fun j hj => hmem2 _ (by right; rw [r2]; bv_omega) (by right; rw [r10]; bv_omega))
  have kp : ∀ (k : Word) (w : Word), 36 ≤ k.toNat → k.toNat ≤ 60 →
      read S1.mem (s.getReg 2#5 + (4294967232#32 + k)) 4 = w →
      read S2.mem (s.getReg 2#5 + (4294967232#32 + k)) 4 = w := fun k w h1 h2 h => by
    rw [← BitVec.add_assoc, keep k h1 h2, BitVec.add_assoc, h]
  -- block B and the `ret`
  obtain ⟨n3, T, hrun3, hpcT, hcsT, hmemT, hcanT, hvalT⟩ := poly_part_b A s S2
    (by rw [hpc2, r1]) (codeAt_of_rom hcode (by rw [hlen]; simp only [ROM_END]; omega) hrom2) hal
    (by simp only [ROM_END]; omega) hsp16 (by simp only [ROM_END]; omega) (by simp only [RAM_END]; omega)
    ho4 hos (by simp only [RAM_END]; omega) hra
    (by rw [cs 2#5 (by rv_callee_saved), r2]) (by rw [cs 9#5 (by rv_callee_saved), r9])
    (by rw [cs 18#5 (by rv_callee_saved), r18]) (by rw [cs 19#5 (by rv_callee_saved), r19]) (by rw [cs 20#5 (by rv_callee_saved), r20])
    (fun r h1 h2 => by rw [cs r (by unfold calleeSaved; right; right; right; omega), r22 r h1 h2])
    (kp 60#32 _ (by decide) (by decide) k1) (kp 56#32 _ (by decide) (by decide) k8)
    (kp 52#32 _ (by decide) (by decide) k9) (kp 48#32 _ (by decide) (by decide) k18)
    (kp 44#32 _ (by decide) (by decide) k19) (kp 40#32 _ (by decide) (by decide) k20)
    (kp 36#32 _ (by decide) (by decide) k21) hcanon2
  refine ⟨87 + n2 + n3, T, by rw [run_add, run_add, hrun1, Option.bind_some, hrun2, Option.bind_some, hrun3],
    hpcT, ⟨hcanT, ?_⟩, hcsT, ?_⟩
  · rw [hvalT, hval2, show (32#32 : Word).toNat = 32 from rfl,
      Finset.sum_congr rfl (fun i hi => by rw [(table4 htab1 i (Finset.mem_range.mp hi)).2]), he1, poly4]
  · intro a ha hb
    rw [hmemT a hb, hmem2 a (by rw [r2]; bv_omega) (by rw [r10]; bv_omega), hmem1 a (by bv_omega)]

end RV
