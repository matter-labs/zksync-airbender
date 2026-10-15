import Slop.RV.Blake.Steps

/-! The compression's results from the chain of `G`s (`Steps`), the counter, `v12`, `v14`. -/

namespace RV.Blake
open _root_.RV.Sym
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option hygiene false in
local notation "V[" i "]" => Pool.val c Blake.σ.pool i

/-- The state words. -/
def H (c : Ctx) : Vector Word 8 := #v[V[37], V[38], V[39], V[40], V[36], V[43], V[44], V[45]]

theorem t2 (c : Ctx) : V[42] = V[35] + V[11] := by
  sym_unfold [11, 35]
  op_cluster

theorem v12 (c : Ctx) : V[52] = V[42] ^^^ Spec.IV 4 := by
  sym_unfold [42]
  sym_generalize
  simp only [alu]; rfl

theorem v14 (c : Ctx) (hl : V[12] = 0#32 ∨ V[12] = 1#32) :
    V[107] = (if decide (V[12] = 1#32) = true then 0xFFFFFFFF#32 else 0#32) ^^^ Spec.IV 6 := by
  sym_unfold [12]
  revert hl
  sym_generalize
  intro hl
  rcases hl with rfl | rfl <;> decide

theorem out0 (c : Ctx) : V[1383] = (H c)[0] ^^^ (S56 c)[0] ^^^ (S56 c)[8] := by
  show V[1383] = V[37] ^^^ V[1303] ^^^ V[1365]
  sym_unfold [37, 1303, 1365]
  sym_generalize
  simp only [alu]
  ac_rfl

theorem out1 (c : Ctx) : V[1384] = (H c)[1] ^^^ (S56 c)[1] ^^^ (S56 c)[9] := by
  show V[1384] = V[38] ^^^ V[1324] ^^^ V[1373]
  sym_unfold [38, 1324, 1373]
  sym_generalize
  simp only [alu]
  ac_rfl

theorem out2 (c : Ctx) : V[1387] = (H c)[2] ^^^ (S56 c)[2] ^^^ (S56 c)[10] := by
  show V[1387] = V[39] ^^^ V[1353] ^^^ V[1315]
  sym_unfold [39, 1315, 1353]
  sym_generalize
  simp only [alu]
  ac_rfl

theorem out3 (c : Ctx) : V[1388] = (H c)[3] ^^^ (S56 c)[3] ^^^ (S56 c)[11] := by
  show V[1388] = V[40] ^^^ V[1364] ^^^ V[1331]
  sym_unfold [40, 1331, 1364]
  sym_generalize
  simp only [alu]
  ac_rfl

theorem out4 (c : Ctx) : V[1391] = (H c)[4] ^^^ (S56 c)[4] ^^^ (S56 c)[12] := by
  show V[1391] = V[36] ^^^ V[1380] ^^^ V[1329]
  sym_unfold [36, 1329, 1380]
  sym_generalize
  simp only [alu]
  ac_rfl

theorem out5 (c : Ctx) : V[1392] = (H c)[5] ^^^ (S56 c)[5] ^^^ (S56 c)[13] := by
  show V[1392] = V[43] ^^^ V[1325] ^^^ V[1363]
  sym_unfold [43, 1325, 1363]
  sym_generalize
  simp only [alu]
  ac_rfl

theorem out6 (c : Ctx) : V[1395] = (H c)[6] ^^^ (S56 c)[6] ^^^ (S56 c)[14] := by
  show V[1395] = V[44] ^^^ V[1341] ^^^ V[1370]
  sym_unfold [44, 1341, 1370]
  sym_generalize
  simp only [alu]
  ac_rfl

theorem out7 (c : Ctx) : V[1396] = (H c)[7] ^^^ (S56 c)[7] ^^^ (S56 c)[15] := by
  show V[1396] = V[45] ^^^ V[1379] ^^^ V[1313]
  sym_unfold [45, 1313, 1379]
  sym_generalize
  simp only [alu]
  ac_rfl

attribute [local irreducible] RV.Sym.Pool.val in
theorem rounds (c : Ctx) :
    Spec.round (M c) (Spec.SIGMA 6) (Spec.round (M c) (Spec.SIGMA 5) (Spec.round (M c) (Spec.SIGMA 4)
      (Spec.round (M c) (Spec.SIGMA 3) (Spec.round (M c) (Spec.SIGMA 2) (Spec.round (M c) (Spec.SIGMA 1)
      (Spec.round (M c) (Spec.SIGMA 0) (S0 c))))))) = S56 c := by
  simp only [Spec.round]
  rw [step1 c, step2 c, step3 c, step4 c, step5 c, step6 c, step7 c, step8 c, step9 c, step10 c, step11 c, step12 c, step13 c, step14 c, step15 c, step16 c, step17 c, step18 c, step19 c, step20 c, step21 c, step22 c, step23 c, step24 c, step25 c, step26 c, step27 c, step28 c, step29 c, step30 c, step31 c, step32 c, step33 c, step34 c, step35 c, step36 c, step37 c, step38 c, step39 c, step40 c, step41 c, step42 c, step43 c, step44 c, step45 c, step46 c, step47 c, step48 c, step49 c, step50 c, step51 c, step52 c, step53 c, step54 c, step55 c, step56 c]

attribute [local irreducible] RV.Sym.Pool.val in
/-- The eight results are the compression of the state, the block, the new counter and `last`. -/
theorem values (c : Ctx) (hl : V[12] = 0#32 ∨ V[12] = 1#32) :
    #v[V[1383], V[1384], V[1387], V[1388], V[1391], V[1392], V[1395], V[1396]] =
      Spec.compress (H c) (M c) (V[35] + V[11]) (V[12] = 1#32) := by
  have e0 : (#v[(H c)[0], (H c)[1], (H c)[2], (H c)[3], (H c)[4], (H c)[5], (H c)[6], (H c)[7], Spec.IV 0,
      Spec.IV 1, Spec.IV 2, Spec.IV 3, (V[35] + V[11]) ^^^ Spec.IV 4, Spec.IV 5,
      (if decide (V[12] = 1#32) = true then 0xFFFFFFFF#32 else 0#32) ^^^ Spec.IV 6, Spec.IV 7] : Vector Word 16) =
      S0 c := by
    rw [← t2 c, ← v12 c, ← v14 c hl]; rfl
  simp only [Spec.compress]
  rw [e0, rounds]
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  interval_cases i
  all_goals first
    | exact out0 c
    | exact out1 c
    | exact out2 c
    | exact out3 c
    | exact out4 c
    | exact out5 c
    | exact out6 c
    | exact out7 c

end RV.Blake
