import Slop.JumpBranchSlt.RVData
import Slop.JumpBranchSlt.Branch
import Slop.JumpBranchSlt.Jump
import Slop.JumpBranchSlt.RVDecoder
import Slop.ISA.RV.Step

/-! Row calculation of the RV comparison, branch and jump claims: from the imported constraints of one row, its
    decoder data (`comparisonData` / `branchData` / `jumpData`), its operand reads at the RV pre-state and the bounds
    (`RVRowFacts`, all derived from the trace in `RVTraceSoundness.lean`), `RV.exec` of the row's instruction succeeds
    and gives the claimed post-state. Reuses the Sail-free word-level lemmas `signed_destination`,
    `unsigned_destination`, `branch_resolution`, `branch_pc`, `jump_link`, `jump_pc`.

    Alignment: a taken branch and both jumps land on a 4-byte aligned target because of the circuit's bit-1 check
    (`cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs`: the `JumpCleanupOffset` lookup gives bit 1 of the raw
    target's low limb and the cleaned low limb; `(is_jal + is_jalr + should_jump_if_branch) * bit1 = 0`; imported as
    lookup 7 and assertion 7, used by `branch_pc` / `jump_pc`), given a 4-byte aligned PC (fetch guard) and an even
    offset (`decode_jal_even`, `decode_branch_even`). For JALR the cleaned limb is the raw one with bit 0 cleared
    (`&&& 0xfffffffe`, our spec's `&&& ~~~1`). -/

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace

/-- What the trace gives for one JumpBranchSlt row at RV pre-state `s` with decoder data `data`. -/
structure RVRowFacts {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (s : RV.State) (data : DecoderData Unit) :
    Prop where
  constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  pcWord : Word.mk (w 0).val (w 1).val = Word.ofBitVec s.pc
  pcAligned : s.pc.toNat % 4 = 0
  immediateLo : w 8 = (data.immediate.lo : ZMod p)
  immediateHi : w 9 = (data.immediate.hi : ZMod p)
  funct3 : w 10 = (data.funct3 : ZMod p)
  flags : ∀ i : Fin 5, w (11 + i.val) = if data.mask.testBit i.val then 1 else 0
  left : s.getReg data.rs1 = (Word.mk (w 22).val (w 23).val).toBitVec
  right : s.getReg data.rs2 = (Word.mk (w 26).val (w 27).val).toBitVec
  leftBound : (Word.mk (w 22).val (w 23).val).Bounded
  rightBound : (Word.mk (w 26).val (w 27).val).Bounded
  finalHi : (w 17).val < limbBase

private theorem same_refl (s : RV.State) : RV.Same s s := ⟨rfl, fun _ => rfl, rfl, rfl⟩

/-- A jump's post-state (`RV.exec`: set PC, then link) agrees with the claimed one (link, then set PC). -/
private theorem same_link (s : RV.State) (rd : RV.Reg) (t v d : RV.Word) (hv : rd ≠ 0 → d = v) :
    RV.Same ((s.setPC t).setReg rd v) ((s.setReg rd d).setPC t) := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro i
  simp only [RV.State.getReg, RV.State.setPC, RV.State.setReg]
  by_cases hi : i = 0
  · simp [hi]
  · by_cases hr : i = rd
    · subst hr
      simp [hv hi]
    · simp [hr]

private theorem flag {p : Nat} {w : Nat → ZMod p} {mask : Nat}
    (flags : ∀ i : Fin 5, w (11 + i.val) = if mask.testBit i.val then 1 else 0) (k : Fin 5) (b : Bool)
    (bit : mask.testBit k.val = b) : w (11 + k.val) = if b then 1 else 0 := by
  rw [flags k, bit]

private theorem word_eq {x : Word} {a b : Nat} (lo : x.lo = a) (hi : x.hi = b) : x = ⟨a, b⟩ := by
  cases x
  simp_all

private theorem zero_limbs {p : Nat} [Fact p.Prime] {a b : ZMod p} (bound : (Word.mk a.val b.val).Bounded)
    (zero : (Word.mk a.val b.val).toBitVec = 0) : a = 0 ∧ b = 0 := by
  have eq := Word.eq_zero_of_bounded bound zero
  simp only [Word.mk.injEq, ZMod.val_eq_zero] at eq
  exact eq

private theorem pc_bound {p : Nat} {w : Nat → ZMod p} {pc : RV.Word}
    (pcWord : Word.mk (w 0).val (w 1).val = Word.ofBitVec pc) : (Word.mk (w 0).val (w 1).val).Bounded :=
  pcWord ▸ Word.ofBitVec_bound pc

private theorem pc_bits {p : Nat} {w : Nat → ZMod p} {pc : RV.Word}
    (pcWord : Word.mk (w 0).val (w 1).val = Word.ofBitVec pc) : (Word.mk (w 0).val (w 1).val).toBitVec = pc := by
  rw [pcWord, Word.ofBitVec_roundtrip]

private theorem pc_low_aligned {p : Nat} {w : Nat → ZMod p} {pc : RV.Word}
    (pcWord : Word.mk (w 0).val (w 1).val = Word.ofBitVec pc) (aligned : pc.toNat % 4 = 0) : (w 0).val % 4 = 0 := by
  have lo := congrArg Word.lo pcWord
  simp only [Word.ofBitVec, limbBase] at lo
  omega

/-- `comparison_pc` over bare limbs: a selected comparison row's final PC is its PC plus four. -/
theorem rv_comparison_pc {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (pcLo : initial.lo = (w 0).val) (pcHi : initial.hi = (w 1).val)
    (finalPCLo : final.lo = (w 16).val) (finalPCHi : final.hi = (w 17).val)
    (initialPCLoBound : initial.lo < limbBase) (pcAligned : initial.lo % 4 = 0)
    (finalPCHiBound : final.hi < limbBase) :
    final.toBitVec = initial.toBitVec + 4 := by
  have bounds := local_ranges h
  have cleanup := (lookup_values hp h).2.2.2.2
  obtain ⟨c, b, cb, bb, hc, hb⟩ := pc_carries h
  have branch := Verification.assertion_of_holds h
    ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, other.2.2] at branch
  have low := Verification.assertion_of_holds h
    ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨6, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected, other.1, other.2.1, other.2.2, branch, hc, hb] at low high
  have initialLo : w 0 = (initial.lo : ZMod p) := by
    rw [pcLo]; exact (ZMod.natCast_zmod_val _).symm
  have initialHi : w 1 = (initial.hi : ZMod p) := by
    rw [pcHi]; exact (ZMod.natCast_zmod_val _).symm
  have lowEq : (initial.lo : ZMod p) + 4 = (w 36).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [initialLo] at low
    linear_combination low
  have lowNat : initial.lo + 4 = (w 36).val + 65536 * c :=
    bounded_nat_eq (F := ZMod p) (p := p)
      (by unfold limbBase at initialPCLoBound; omega)
      (by have := bounds.2.2.2; unfold limbBase at this; omega)
      (by exact_mod_cast lowEq)
  have aligned : (w 36).val % 4 = 0 := by omega
  have finalLo : final.lo = (w 36).val := by
    rw [finalPCLo, cleanup, aligned, Nat.sub_zero, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by have := bounds.2.2.2; unfold limbBase at this; omega)]
  have finalHi : w 17 = (final.hi : ZMod p) := by
    rw [finalPCHi]; exact (ZMod.natCast_zmod_val _).symm
  have initialBound : initial.Bounded := ⟨initialPCLoBound, pcHi ▸ bounds.2.2.1⟩
  have finalBound : final.Bounded := ⟨finalLo ▸ bounds.2.2.2, finalPCHiBound⟩
  have result := Word.add_of_limbs (by omega : 196608 < p)
    (left := initial) (right := ⟨0, 0⟩) (immediate := ⟨4, 0⟩)
    (output := final) initialBound (by constructor <;> decide)
    (by constructor <;> decide) finalBound (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa [finalLo] using lowEq)
    (by
      rw [initialHi, finalHi] at high
      dsimp
      linear_combination high)
  simpa [Word.toBitVec, Word.value, limbBase] using result

/-- One comparison row is one `RV.exec` of its instruction, with the claimed post-state. -/
theorem rv_comparison_exec {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {w : Nat → ZMod p}
    {input : Comparison.RVInput} {output : Circuit.Output}
    (facts : RVRowFacts w input.before (comparisonData input))
    (outputLo : output.destination.lo = (w 30).val) (outputHi : output.destination.hi = (w 31).val)
    (finalPCLo : output.pc.lo = (w 16).val) (finalPCHi : output.pc.hi = (w 17).val) :
    ∃ s', RV.exec input.before (Comparison.rvInstruction input) = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec) := by
  have h := facts.constraints
  have mask : (comparisonData input).mask = 4 := by unfold comparisonData; split <;> rfl
  have rs1Eq : (comparisonData input).rs1 = input.rs1 := by unfold comparisonData; split <;> rfl
  have f := facts.flags
  rw [mask] at f
  have s11 : w 11 = 0 := by simpa using flag f ⟨0, by decide⟩ false (by decide)
  have s12 : w 12 = 0 := by simpa using flag f ⟨1, by decide⟩ false (by decide)
  have s13 : w 13 = 1 := by simpa using flag f ⟨2, by decide⟩ true (by decide)
  have s14 : w 14 = 0 := by simpa using flag f ⟨3, by decide⟩ false (by decide)
  have s15 : w 15 = 0 := by simpa using flag f ⟨4, by decide⟩ false (by decide)
  -- PC + 4.
  have pcNext : output.pc.toBitVec = input.before.pc + 4 := by
    rw [← pc_bits facts.pcWord]
    exact rv_comparison_pc hp h s13 ⟨s11, s12, s14⟩ rfl rfl finalPCLo finalPCHi
      (pc_bound facts.pcWord).1 (pc_low_aligned facts.pcWord facts.pcAligned) (finalPCHi ▸ facts.finalHi)
  have leftValue := facts.left
  rw [rs1Eq] at leftValue
  let L : Word := ⟨(w 22).val, (w 23).val⟩
  let R : Word := ⟨(w 26).val, (w 27).val⟩
  have funct3 := facts.funct3
  have immLo := facts.immediateLo
  have immHi := facts.immediateHi
  have rightValue := facts.right
  -- Result per opcode: `right` is the second register (register forms) or the immediate (x0 is read).
  have result : ∀ (right : Word) (signed : Bool), right.Bounded →
      w 26 + w 8 = (right.lo : ZMod p) → w 27 + w 9 = (right.hi : ZMod p) →
      w 10 = (if signed then 2 else 3 : ZMod p) →
      output.destination.toBitVec = RV.alu (if signed then .slt else .sltu) L.toBitVec right.toBitVec := by
    intro right signed rightBound lo hi tag
    have operands : w 22 = (L.lo : ZMod p) ∧ w 23 = (L.hi : ZMod p) ∧
        w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p) :=
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, lo, hi⟩
    have leftBound : L.Bounded := facts.leftBound
    have destination : output.destination.toBitVec = BitVec.ofNat 32 output.destination.value := rfl
    cases signed
    · have value := unsigned_destination hp h s13 ⟨s11, s12, s14⟩ (by simpa using tag) s15 operands
        ⟨outputLo, outputHi⟩ facts.leftBound rightBound
      have ult : L.toBitVec.ult right.toBitVec = decide (L.value < right.value) := by
        rw [BitVec.ult, Word.toBitVec_toNat leftBound, Word.toBitVec_toNat rightBound]
      rw [destination, value]
      by_cases lt : L.value < right.value <;> simp [RV.alu, ult, lt]
    · have value := signed_destination hp h s13 ⟨s11, s12, s14⟩ (by simpa using tag) s15 operands
        ⟨outputLo, outputHi⟩ facts.leftBound rightBound
      rw [destination, value]
      by_cases lt : L.toBitVec.toInt < right.toBitVec.toInt <;> simp [RV.alu, BitVec.slt, lt]
  obtain ⟨opcode, left, right, pc, rs1, rs2, rd, imm, before⟩ := input
  dsimp only at leftValue rightValue immLo immHi funct3 pcNext ⊢
  have register (signed : Bool) (tag : w 10 = (if signed then 2 else 3 : ZMod p)) (z8 : w 8 = 0) (z9 : w 9 = 0)
      (rightValue : before.getReg rs2 = R.toBitVec) :
      RV.Same (before.setReg rd (RV.alu (if signed then .slt else .sltu) (before.getReg rs1)
          (before.getReg rs2))).nextInstr
        ((before.setReg rd output.destination.toBitVec).setPC output.pc.toBitVec) := by
    have destination := result R signed facts.rightBound
      (by rw [z8, add_zero]; exact (ZMod.natCast_zmod_val _).symm)
      (by rw [z9, add_zero]; exact (ZMod.natCast_zmod_val _).symm) tag
    rw [leftValue, rightValue, destination, pcNext]
    exact same_refl _
  have immediate (signed : Bool) (tag : w 10 = (if signed then 2 else 3 : ZMod p))
      (z8 : w 8 = ((Word.ofBitVec (imm.signExtend 32)).lo : ZMod p))
      (z9 : w 9 = ((Word.ofBitVec (imm.signExtend 32)).hi : ZMod p))
      (rightValue : before.getReg 0 = R.toBitVec) :
      RV.Same (before.setReg rd (RV.alu (if signed then .slt else .sltu) (before.getReg rs1)
          (imm.signExtend 32))).nextInstr
        ((before.setReg rd output.destination.toBitVec).setPC output.pc.toBitVec) := by
    have zero := zero_limbs facts.rightBound (by rw [← rightValue]; rfl)
    have destination := result (Word.ofBitVec (imm.signExtend 32)) signed (Word.ofBitVec_bound _)
      (by rw [zero.1, zero_add]; exact z8) (by rw [zero.2, zero_add]; exact z9) tag
    rw [Word.ofBitVec_roundtrip] at destination
    rw [leftValue, destination, pcNext]
    exact same_refl _
  cases opcode
  · simp only [comparisonData] at leftValue rightValue immLo immHi funct3
    exact ⟨_, rfl, register true (by simpa using funct3) (by simpa using immLo) (by simpa using immHi) rightValue⟩
  · simp only [comparisonData] at leftValue rightValue immLo immHi funct3
    exact ⟨_, rfl, immediate true (by simpa using funct3) immLo immHi rightValue⟩
  · simp only [comparisonData] at leftValue rightValue immLo immHi funct3
    exact ⟨_, rfl, register false (by simpa using funct3) (by simpa using immLo) (by simpa using immHi) rightValue⟩
  · simp only [comparisonData] at leftValue rightValue immLo immHi funct3
    exact ⟨_, rfl, immediate false (by simpa using funct3) immLo immHi rightValue⟩

private theorem ult_value {L R : Word} (lb : L.Bounded) (rb : R.Bounded) :
    L.toBitVec.ult R.toBitVec = decide (L.value < R.value) := by
  rw [BitVec.ult, Word.toBitVec_toNat lb, Word.toBitVec_toNat rb]

private theorem offset_even {offset : RV.Word} (even : offset.toNat % 2 = 0) : (Word.ofBitVec offset).lo % 2 = 0 := by
  simp only [Word.ofBitVec, limbBase]
  omega

/-- One branch row is one `RV.exec` of its instruction: the next PC is the taken target or PC + 4. -/
theorem rv_branch_exec {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {w : Nat → ZMod p}
    {input : Branch.RVInput} {output : Circuit.Output}
    (facts : RVRowFacts w input.before (branchData input))
    (even : (input.encodedOffset.signExtend 32).toNat % 2 = 0)
    (finalPCLo : output.pc.lo = (w 16).val) (finalPCHi : output.pc.hi = (w 17).val) :
    ∃ s', RV.exec input.before (Branch.rvInstruction input) = some s' ∧
      RV.Same s' (input.before.setPC output.pc.toBitVec) := by
  have h := facts.constraints
  have f := facts.flags
  change ∀ i : Fin 5, w (11 + i.val) = if (24 : Nat).testBit i.val then 1 else 0 at f
  have s11 : w 11 = 0 := by simpa using flag f ⟨0, by decide⟩ false (by decide)
  have s12 : w 12 = 0 := by simpa using flag f ⟨1, by decide⟩ false (by decide)
  have s13 : w 13 = 0 := by simpa using flag f ⟨2, by decide⟩ false (by decide)
  have s14 : w 14 = 1 := by simpa using flag f ⟨3, by decide⟩ true (by decide)
  let L : Word := ⟨(w 22).val, (w 23).val⟩
  let R : Word := ⟨(w 26).val, (w 27).val⟩
  have lb : L.Bounded := facts.leftBound
  have rb : R.Bounded := facts.rightBound
  have tag : (w 10).val = Branch.rvFunct3 input.cond := by
    have t := facts.funct3
    change w 10 = (Branch.rvFunct3 input.cond : ZMod p) at t
    rw [t, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := rvFunct3_lt input.cond; omega)]
  have resolution := branch_resolution hp h s14 ⟨s11, s12, s13⟩
    (by rw [tag]; have := rvFunct3_lt input.cond; omega)
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
      (ZMod.natCast_zmod_val _).symm⟩ lb rb
  rw [tag] at resolution
  let taken := input.cond.holds L.toBitVec R.toBitVec
  have resolved : w 45 = if taken then 1 else 0 := by
    rw [resolution]
    have ult := ult_value lb rb
    cases hc : input.cond <;> simp only [taken, hc, Branch.rvFunct3, RV.Cond.holds]
    · by_cases e : L.toBitVec = R.toBitVec <;> simp [e]
    · by_cases e : L.toBitVec = R.toBitVec <;> simp [e]
    · by_cases e : L.toBitVec.toInt < R.toBitVec.toInt <;> simp [e, BitVec.slt]
    · by_cases e : L.toBitVec.toInt < R.toBitVec.toInt <;> simp [e, BitVec.slt]
    · by_cases e : L.value < R.value <;> simp [e, ult]
    · by_cases e : L.value < R.value <;> simp [e, ult]
  obtain ⟨pcEq, aligned⟩ := branch_pc hp taken h s14 ⟨s11, s12, s13⟩ resolved
    (initial := ⟨(w 0).val, (w 1).val⟩) (offset := Word.ofBitVec (input.encodedOffset.signExtend 32))
    ⟨rfl, rfl, facts.immediateLo, facts.immediateHi, finalPCLo, finalPCHi⟩
    (pc_bound facts.pcWord).1 (pc_low_aligned facts.pcWord facts.pcAligned) (Word.ofBitVec_bound _)
    (offset_even even) (finalPCHi ▸ facts.finalHi)
  rw [pc_bits facts.pcWord, Word.ofBitVec_roundtrip] at pcEq
  have leftValue : input.before.getReg input.rs1 = L.toBitVec := facts.left
  have rightValue : input.before.getReg input.rs2 = R.toBitVec := facts.right
  have holds : input.cond.holds (input.before.getReg input.rs1) (input.before.getReg input.rs2) = taken := by
    rw [leftValue, rightValue]
  cases hk : taken
  · rw [hk] at holds pcEq
    refine ⟨_, RV.exec_branch_f _ _ _ _ _ holds, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at pcEq
    rw [pcEq]
    exact same_refl _
  · rw [hk] at holds pcEq
    simp only [↓reduceIte] at pcEq
    refine ⟨_, RV.exec_branch_t _ _ _ _ _ holds (pcEq ▸ aligned), ?_⟩
    rw [pcEq]
    exact same_refl _

/-- One JAL/JALR row is one `RV.exec` of its instruction: `rd` := PC + 4 (x0: discarded), PC := the target. -/
theorem rv_jump_exec {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {w : Nat → ZMod p}
    {input : Jump.RVInput} {output : Circuit.Output}
    (facts : RVRowFacts w input.before (jumpData input))
    (even : ∀ offset, input.instruction = .jal offset → (offset.signExtend 32).toNat % 2 = 0)
    (outputLo : output.destination.lo = (w 30).val) (outputHi : output.destination.hi = (w 31).val)
    (finalPCLo : output.pc.lo = (w 16).val) (finalPCHi : output.pc.hi = (w 17).val) :
    ∃ s', RV.exec input.before (Jump.rvInstruction input) = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec) := by
  have h := facts.constraints
  have one : (1 : ZMod p) ≠ 0 := one_ne_zero
  have destination : output.destination = ⟨(w 30).val, (w 31).val⟩ := word_eq outputLo outputHi
  have pcBits := pc_bits facts.pcWord
  obtain ⟨instruction, source, offset, pc, rs1, rd, before⟩ := input
  have f := facts.flags
  cases instruction with
  | jal imm =>
    have bits (k : Fin 4) : Nat.testBit (if rd = 0 then 17 else 1) k.val = (k.val == 0) := by
      split <;> fin_cases k <;> decide
    change ∀ i : Fin 5, w (11 + i.val) = if (if rd = 0 then 17 else 1 : Nat).testBit i.val then 1 else 0 at f
    have s11 : w 11 = 1 := by simpa using flag f ⟨0, by decide⟩ _ (bits ⟨0, by decide⟩)
    have s12 : w 12 = 0 := by simpa using flag f ⟨1, by decide⟩ _ (bits ⟨1, by decide⟩)
    have s13 : w 13 = 0 := by simpa using flag f ⟨2, by decide⟩ _ (bits ⟨2, by decide⟩)
    have s14 : w 14 = 0 := by simpa using flag f ⟨3, by decide⟩ _ (bits ⟨3, by decide⟩)
    have s15 (nz : rd ≠ 0) : w 15 = 0 := by
      simpa using flag f ⟨4, by decide⟩ false (by rw [if_neg nz]; decide)
    obtain ⟨link, _⟩ := jump_link hp h (by rw [s11, s12, add_zero]) ⟨s13, s14⟩ ⟨rfl, rfl⟩
      (pc_bound facts.pcWord).1
    obtain ⟨target, aligned⟩ := jump_pc hp false h (base := ⟨(w 0).val, (w 1).val⟩)
      (offset := Word.ofBitVec (imm.signExtend 32)) (by simp [s11, s12]) ⟨s13, s14⟩
      ⟨rfl, rfl, facts.immediateLo, facts.immediateHi, finalPCLo, finalPCHi⟩ (pc_bound facts.pcWord).1
      (fun h => nomatch h) (Word.ofBitVec_bound _)
      (fun _ => ⟨by have := pc_low_aligned facts.pcWord facts.pcAligned; show (w 0).val % 2 = 0; omega,
        offset_even (even imm rfl)⟩) (finalPCHi ▸ facts.finalHi)
    simp only [Bool.false_eq_true, ↓reduceIte, Word.ofBitVec_roundtrip] at target
    rw [pcBits] at target link
    dsimp only at target aligned link ⊢
    refine ⟨_, RV.exec_jal _ _ _ (target ▸ aligned), ?_⟩
    rw [← target]
    apply same_link
    intro nz
    rw [destination, link, ite_cond_eq_false _ _ (by rw [s15 nz]; exact eq_false one.symm)]
  | jalr imm =>
    have bits (k : Fin 4) : Nat.testBit (if rd = 0 then 18 else 2) k.val = (k.val == 1) := by
      split <;> fin_cases k <;> decide
    change ∀ i : Fin 5, w (11 + i.val) = if (if rd = 0 then 18 else 2 : Nat).testBit i.val then 1 else 0 at f
    have s11 : w 11 = 0 := by simpa using flag f ⟨0, by decide⟩ _ (bits ⟨0, by decide⟩)
    have s12 : w 12 = 1 := by simpa using flag f ⟨1, by decide⟩ _ (bits ⟨1, by decide⟩)
    have s13 : w 13 = 0 := by simpa using flag f ⟨2, by decide⟩ _ (bits ⟨2, by decide⟩)
    have s14 : w 14 = 0 := by simpa using flag f ⟨3, by decide⟩ _ (bits ⟨3, by decide⟩)
    have s15 (nz : rd ≠ 0) : w 15 = 0 := by
      simpa using flag f ⟨4, by decide⟩ false (by rw [if_neg nz]; decide)
    obtain ⟨link, _⟩ := jump_link hp h (by rw [s11, s12, zero_add]) ⟨s13, s14⟩ ⟨rfl, rfl⟩
      (pc_bound facts.pcWord).1
    obtain ⟨target, aligned⟩ := jump_pc hp true h (base := ⟨(w 22).val, (w 23).val⟩)
      (offset := Word.ofBitVec (imm.signExtend 32)) (by simp [s11, s12]) ⟨s13, s14⟩
      ⟨rfl, rfl, facts.immediateLo, facts.immediateHi, finalPCLo, finalPCHi⟩ facts.leftBound.1
      (fun _ => facts.leftBound.2) (Word.ofBitVec_bound _) (fun h => nomatch h) (finalPCHi ▸ facts.finalHi)
    have mask : (0xfffffffe : BitVec 32) = ~~~1 := by decide
    have leftValue : before.getReg rs1 = (Word.mk (w 22).val (w 23).val).toBitVec := facts.left
    simp only [↓reduceIte, Word.ofBitVec_roundtrip, mask, ← leftValue] at target
    rw [pcBits] at link
    dsimp only at target aligned link ⊢
    refine ⟨_, RV.exec_jalr _ _ _ _ (target ▸ aligned), ?_⟩
    rw [← target]
    apply same_link
    intro nz
    rw [destination, link, ite_cond_eq_false _ _ (by rw [s15 nz]; exact eq_false one.symm)]

end Airbender.JumpBranchSlt.Proofs
