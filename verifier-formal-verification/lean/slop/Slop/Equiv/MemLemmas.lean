import Slop.Equiv.Run

/-! Address facts for Sail's memory path on Airbender (machine mode, no pointer masking, no paging). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

theorem pm_transform_PA_zero (a : BitVec 32) : pm_transform_PA (.Virtaddr a) 0 = .Virtaddr a := by
  simp only [pm_transform_PA, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, BitVec.extractLsb,
    Functions.xlen]
  congr 1; apply BitVec.eq_of_toNat_eq; simp

theorem is_aligned_vaddr_iff (a : BitVec 32) (n : Nat) :
    is_aligned_vaddr (.Virtaddr a) n = decide (a.toNat % n = 0) := by
  simp only [is_aligned_vaddr, BitVec.toNatInt]
  rw [Int.ofNat_eq_natCast, Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _)]
  by_cases h : a.toNat % n = 0 <;> simp [h] <;> omega

theorem is_aligned_paddr_iff (a : BitVec 32) (n : Nat) :
    is_aligned_paddr (.Physaddr (zero_extend (m := 34) a)) n = decide (a.toNat % n = 0) := by
  simp only [is_aligned_paddr, BitVec.toNatInt, zero_extend, Sail.BitVec.zeroExtend]
  rw [Int.ofNat_eq_natCast, Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _)]
  have : (BitVec.zeroExtend 34 a).toNat = a.toNat := by simp; omega
  rw [this]
  by_cases h : a.toNat % n = 0 <;> simp [h] <;> omega

theorem is_aligned_paddr_iff' (x : physaddrbits) (n : Nat) :
    is_aligned_paddr (.Physaddr x) n = decide (x.toNat % n = 0) := by
  simp only [is_aligned_paddr, BitVec.toNatInt]
  rw [Int.ofNat_eq_natCast, Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _)]
  by_cases h : x.toNat % n = 0 <;> simp [h] <;> omega

theorem zero_extend_toNat (a : BitVec 32) {m : Nat} (h : 32 ≤ m) : (zero_extend (m := m) a).toNat = a.toNat := by
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
  have := a.isLt
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) h))

theorem pma_regions_eq {σ : FState} (hs : Airbender.Sys σ) : σ.regs .pma_regions = Airbender.memoryMap := by
  rw [hs .pma_regions rfl]; rfl

theorem match_ram (a : BitVec 32) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (h1 : Airbender.RAM_START ≤ a.toNat)
    (h2 : a.toNat + w ≤ Airbender.RAM_END) :
    matching_pma_region Airbender.memoryMap (.Physaddr (zero_extend (m := 34) a)) w =
      some (Airbender.region Airbender.RAM_START (Airbender.RAM_END - Airbender.RAM_START) true true false) := by
  simp only [Airbender.RAM_START, Airbender.RAM_END] at h1 h2
  simp only [matching_pma_region, matching_pma_region_bits_range, Airbender.memoryMap, Airbender.region,
    range_subset, zopz0zIzJ_u, BitVec.toNatInt, zero_extend, Sail.BitVec.zeroExtend, bits_of_physaddr, to_bits,
    Airbender.RAM_START, Airbender.RAM_END]
  have hw' : (get_slice_int 64 (↑w) 0 : BitVec 64).toNat = w := by
    simp [get_slice_int, BitVec.toNat_ofInt]; omega
  have ha32 := a.isLt
  have e1 : (BitVec.zeroExtend 64 (BitVec.zeroExtend 34 a)).toNat = a.toNat := by simp; omega
  simp [BitVec.toNat_sub, BitVec.toNat_add, hw', e1]
  rw [if_neg (by omega), if_pos (by omega)]

theorem match_rom (a : BitVec 32) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (h2 : a.toNat + w ≤ Airbender.RAM_START) :
    matching_pma_region Airbender.memoryMap (.Physaddr (zero_extend (m := 34) a)) w =
      some (Airbender.region 0 Airbender.RAM_START true false true) := by
  simp only [Airbender.RAM_START, Airbender.RAM_END] at h2
  simp only [matching_pma_region, matching_pma_region_bits_range, Airbender.memoryMap, Airbender.region,
    range_subset, zopz0zIzJ_u, BitVec.toNatInt, zero_extend, Sail.BitVec.zeroExtend, bits_of_physaddr, to_bits,
    Airbender.RAM_START, Airbender.RAM_END]
  have hw' : (get_slice_int 64 (↑w) 0 : BitVec 64).toNat = w := by
    simp [get_slice_int, BitVec.toNat_ofInt]; omega
  have ha32 := a.isLt
  have e1 : (BitVec.zeroExtend 64 (BitVec.zeroExtend 34 a)).toNat = a.toNat := by simp; omega
  simp [BitVec.toNat_sub, BitVec.toNat_add, hw', e1]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem page_mask_eq :
    (BitVec.updateSubrange ones ((fun x y => x - y) (↑Functions.pagesize_bits : Int) 1).toNat 0 zeros : BitVec 32) =
      0xFFFFF000#32 := by decide

/-- An aligned access of 1, 2 or 4 bytes never crosses a 4 KiB page. -/
theorem same_page (a : BitVec 32) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4) (ha : a.toNat % w = 0) :
    (a &&& 0xFFFFF000#32 == a + BitVec.ofNat 32 w - 1#32 &&& 0xFFFFF000#32) = true := by
  rw [beq_iff_eq]
  have hlt := a.isLt
  have hsum : (a + BitVec.ofNat 32 w - 1#32).toNat = a.toNat + w - 1 := by
    rcases hw with rfl | rfl | rfl <;> simp [BitVec.toNat_add, BitVec.toNat_sub] <;> omega
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and]
  by_cases hi12 : i < 12
  · have : (0xFFFFF000#32 : BitVec 32).getLsbD i = false := by interval_cases i <;> rfl
    simp [this]
  · congr 1
    simp only [BitVec.getLsbD, hsum, Nat.testBit_eq_decide_div_mod_eq]
    congr 1
    interval_cases i <;> rcases hw with rfl | rfl | rfl <;> simp <;> omega

end Slop.Equiv

open Lean Meta Elab Tactic in
/-- Replace each closed bit-vector subterm of the goal (e.g. a mask built from `ones`, `zeros`, shifts) by its value,
each step checked by the kernel. -/
elab "eval_bv" : tactic => withMainContext do
  let g ← getMainGoal
  let ref ← IO.mkRef (#[] : Array Expr)
  forEachExpr (← instantiateMVars (← g.getType)) fun x => do
    unless x.hasMVar || x.hasLooseBVars do
      let ty ← try inferType x catch _ => return
      if ty.isAppOfArity ``BitVec 1 && (← getBitVecValue? x).isNone && !x.isAppOf ``OfNat.ofNat then
        ref.modify (·.push x)
  let mut g := g
  let cands := (← ref.get).qsort (fun a b => a.approxDepth.toNat > b.approxDepth.toNat)
  for x in cands do
    -- widths written as `length y` mention `y`; they are just numbers
    let xc ← Meta.transform x (post := fun e => do
      if e.isAppOfArity ``Sail.BitVec.length 2 then
        if let some n ← (evalNat (e.getArg! 0)).run then return .done (mkNatLit n)
      return .continue)
    if xc.hasFVar then continue
    unless ((← instantiateMVars (← g.getType)).find? (· == x)).isSome do
      continue
    let ty ← inferType x
    let some w ← (evalNat (ty.appArg!)).run | continue
    let v ← try unsafe evalExpr (BitVec w) (mkApp (mkConst ``BitVec) (mkNatLit w)) xc
      catch e => do trace[debug] "eval_bv: eval failed {x}: {e.toMessageData}"; continue
    let lit := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit v.toNat)
    let pf ← try withOptions (fun o => maxRecDepth.set o 1000000) (mkAuxTheorem (← mkEq x lit) (← mkEqRefl x))
      catch e => do trace[debug] "eval_bv: kernel check failed {x}: {e.toMessageData}"; continue
    let r ← try g.rewrite (← g.getType) pf
      catch e => do trace[debug] "eval_bv: rewrite failed {x}: {e.toMessageData}"; continue
    g ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal [g]

/-- Side conditions on the memory path (alignment, page split), from the hypotheses in context. -/
macro "mem_side" : tactic => `(tactic| first
  | (simp only [Int.toNat_zero, Slop.Equiv.pm_transform_PA_zero, Slop.Equiv.is_aligned_vaddr_iff, decide_true,
      decide_false, *] <;> rfl)
  | (simp (disch := decide) only [Slop.Equiv.is_aligned_paddr_iff', Slop.Equiv.zero_extend_toNat, decide_true,
      Bool.true_or, *] <;> rfl)
  | (simp only [Int.toNat_zero, Slop.Equiv.pm_transform_PA_zero, bits_of_virtaddr, BitVec.addInt, BitVec.subInt,
      Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', ones, zeros, Functions.pagesize_bits, Sail.BitVec.length,
      sail_ones]
     eval_bv
     try simp only [BitVec.shiftLeft_zero, BitVec.reduceNot, BitVec.reduceAnd, BitVec.reduceOr]
     first
      | exact Slop.Equiv.same_page _ 4 (by decide) ‹_›
      | exact Slop.Equiv.same_page _ 2 (by decide) ‹_›
      | exact Slop.Equiv.same_page _ 1 (by decide) ‹_›)
  | (simp [SailRV32.not, *]; done))
