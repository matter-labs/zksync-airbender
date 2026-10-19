import Slop.RV.Main.F
import Slop.RV.Merkle.Check

/-! `main`, the Merkle path (both images): `merkle_check(&BLAKE.state)`, from `main + 0x140` (word 80) to
`main + 0x148` (word 82), or stuck in `zksync_os_finish_error` (a wrong root). `merkle_step` is any implementation
of its contract. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0

theorem main_m (U : State) (codeM : List Word) (Am : Word) (codeS : List Word)
    (calleesS : List (Word × List Word)) (FS al len : Nat)
    (hS : ImplementsAtW (Am + 0x1bc#32) codeS calleesS FS (merklePre al len) len merklePost)
    (root : Vector Word 8) (path : List MerkleStep) (rest : List Word)
    (hAm : Am.toNat % 4 = 0) (hAmr : Am.toNat + 4 * 111 + 0x21c + 24 ≤ ROM_END)
    (hSr : (Am + 0x1bc#32).toNat + 4 * codeS.length ≤ ROM_END)
    (hcalr : ∀ c ∈ calleesS, c.1.toNat + 4 * c.2.length ≤ ROM_END)
    (hMal : MERKLE.toNat % al = 0) (hlen : len ≤ 256) (hlen32 : 32 ≤ len) (hFS : ROM_END + 96 + FS ≤ 0x13fff80) (hFS16 : 16 ≤ FS)
    (hpc : U.pc = 0x178#32) (h2 : U.getReg 2#5 = 0x13fff80#32) (h19 : U.getReg 19#5 = 0x1401000#32)
    (hmain : CodeAt U 0x38#32 codeM) (hlenM : codeM.length = 98)
    (hbM : (codeM.drop 80).take 1 = (Code.main.drop 80).take 1)
    (jm : Word) (hjm : codeM[81]? = some jm) (djm : decode jm = some (.jal 1#5 (Am - 0x17c#32)))
    (hcode : CodeAt U Am Code.merkle_check) (herr : CodeAt U (Am + 0x3d4#32) Code.finish_error)
    (hcS : CodeAt U (Am + 0x1bc#32) codeS) (hcal : ∀ c ∈ calleesS, CodeAt U c.1 c.2)
    (hin : U.input = pathInput root path ++ rest) (hd : path.length ≤ 32) :
    ∃ m W, run m U = some W ∧
      (merkleRoot (readWords U.mem 0x1401000#32 8) path = root →
        W.pc = 0x180#32 ∧ (∀ i, calleeSaved i → W.getReg i = U.getReg i) ∧ W.input = rest ∧
        (∀ a : Word, 0x13fff80 ≤ a.toNat → a.toNat < MERKLE.toNat ∨ MERKLE.toNat + len ≤ a.toNat →
          W.mem a = U.mem a) ∧
        (∀ b : Word, b.toNat < ROM_END → W.mem b = U.mem b)) ∧
      (merkleRoot (readWords U.mem 0x1401000#32 8) path ≠ root → AtFinishError W) := by
  have hl : Code.main.length = 98 := by decide +kernel
  obtain ⟨_, e81⟩ := List.getElem?_eq_some_iff.mp hjm
  have eM : (0x38#32 + BitVec.ofNat 32 (4 * 80) + BitVec.ofNat 32 (4 * 1) + (Am - 0x17c#32) : Word) = Am := by
    bv_omega
  set U0 := U.withInput [] with hU0
  have hc : CodeAt U0 (0x38#32 + BitVec.ofNat 32 (4 * 80)) ((Code.main.drop 80).take 1) := fun i h => by
    rw [hU0, withInput_mem]; exact (hbM ▸ codeAt_take (codeAt_drop hmain 80 (by rw [hlenM]; bv_omega)) 1) i h
  obtain ⟨T0, hrun0, hrel0, hrom0, -, -⟩ := block_jal _ MainM.instrs MainM.σ U0 _ (Am - 0x17c#32) [] []
    MainM.dec MainM.run (by rw [hU0, withInput_pc, hpc]; decide) (by decide) (by simp [hl, ROM_END]) hc jm
    (by
      rw [show ((Code.main.drop 80).take 1).length = 1 by decide +kernel,
        show (0x38#32 + BitVec.ofNat 32 (4 * 80) + BitVec.ofNat 32 (4 * 1) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 81) by decide, hU0, withInput_mem]
      exact (hmain 81 (by omega)).trans e81)
    djm (by rw [show ((Code.main.drop 80).take 1).length = 1 by decide +kernel, eM]; exact hAm) (by simp)
    (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 1 (98 - 80) = 1 from rfl] at hrun0
  set S0 := (T0.setPC (0x38#32 + BitVec.ofNat 32 (4 * 80) + BitVec.ofNat 32 (4 * 1) + (Am - 0x17c#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 80) + BitVec.ofNat 32 (4 * 1) + 4) with hS0
  obtain ⟨-, lift⟩ := run_lift _ U0 S0 hrun0 rfl
  have hrunS := lift U.input
  rw [show U0.withInput U.input = U from rfl] at hrunS
  set S := S0.withInput U.input with hSd
  have j : ∀ r : Reg, r ≠ 1#5 → S.getReg r = T0.getReg r := fun r hr => by
    rw [hSd, withInput_getReg, hS0, jal_getReg _ _ _ _ hr]
  have hpcS : S.pc = Am := by rw [hSd, withInput_pc, hS0, jal_pc]; bv_omega
  have hraS : S.getReg 1#5 = 0x180#32 := by rw [hSd, withInput_getReg, hS0, jal_getReg1]; rfl
  have memS : S.mem = U.mem := by rw [hSd, withInput_mem, hS0, jal_mem, hrel0.2.2.2.2]; rfl
  have inS : S.input = U.input := by rw [hSd, withInput_input]
  have csS : ∀ r : Reg, calleeSaved r → S.getReg r = U.getReg r := fun r hr => by
    rw [j r (by rintro rfl; simp [calleeSaved] at hr)]
    rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      exact (hrel0.reg_same _ MainM.run _ (by decide +kernel)).trans (withInput_getReg _ _ _)
  have a0S : S.getReg 10#5 = 0x1401000#32 := by
    rw [j _ (by decide), hrel0.reg_var _ MainM.run 10#5 19 (by decide) (by decide +kernel),
      show (BitVec.ofNat 5 19 : Reg) = 19#5 from rfl, hU0, withInput_getReg, h19]
  have spS : S.getReg 2#5 = 0x13fff80#32 := (csS _ (by rv_callee_saved)).trans h2
  have romS : ∀ b : Word, b.toNat < ROM_END → S.mem b = U.mem b := fun b _ => by rw [memS]
  have hAmr' := hAmr
  have hFS' := hFS
  simp only [ROM_END, RAM_END] at hAmr' hFS'
  obtain ⟨m, T, hT, hok, hbad⟩ := merkle_check_run Am codeS calleesS FS al len hS S (96 + FS) root path rest hpcS
    hAm hAmr hSr hcalr
    (codeAt_of_rom hcode (by rw [show Code.merkle_check.length = 111 from rfl]; simp only [ROM_END]; omega) romS)
    (codeAt_of_rom herr (by rw [show Code.finish_error.length = 6 by decide +kernel]; simp only [ROM_END]; bv_omega)
      romS)
    (codeAt_of_rom hcS hSr romS)
    (fun c hc' => codeAt_of_rom (hcal c hc') (hcalr c hc') romS) hMal hlen hlen32 le_rfl (by omega)
    (by rw [spS]; simp only [ROM_END]; bv_omega) (by rw [spS]; decide) (by rw [spS]; decide) (by rw [hraS]; decide)
    (by rw [a0S]; decide) (by rw [a0S, spS]; decide) (by rw [a0S]; left; decide) (by rw [a0S]; decide)
    (inS.trans hin) hd
  rw [a0S, memS] at hok hbad
  refine ⟨_, T, run_trans hrunS hT, fun h => ?_, hbad⟩
  obtain ⟨t1, t2, t3, t4⟩ := hok h
  refine ⟨by rw [t1, hraS], fun i hi => by rw [t2 i hi, csS i hi], t3, fun a h1 h2' => ?_, fun b hb => ?_⟩
  · rw [t4 a (by rw [spS]; right; exact h1) h2']
  · rw [t4 b (by rw [spS]; left; simp only [ROM_END] at hb; bv_omega)
      (by left; simp only [ROM_END] at hb; rw [show MERKLE.toNat = 0x1401100 from rfl]; omega)]

end RV
