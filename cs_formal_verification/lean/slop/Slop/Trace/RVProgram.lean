import Human.Helpers.Decoder.RVPooledProgram
import Slop.Trace.Program
import Slop.Trace.RVFetch

/-! RV program table: lookup membership, the imported nine-column query, and the native metadata of
    ADD/SUB/ADDI/LUI/AUIPC and LW/SW (`Trace.rvDecoderFields`). Twins of the `ProgramEntry` lemmas in
    `Program.lean`, `PooledProgram.lean` and `ZeroRegister.lean` on `RVProgramEntry` and `RV.Instr`: the query has the
    same definition, so the proofs are the same; the metadata facts are case splits on `RV.Instr`. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- Membership in a family table built from the RV program (as `decoder_member`). -/
theorem rv_decoder_member {Kind : Type} [DecidableEq Kind]
    {p : Nat} [Fact p.Prime] {program : List (RVProgramEntry Kind)}
    {family : Kind} {query : Vector (ZMod p) 9}
    (member : (rvDecoderTable program family).Contains #[] query) :
    ∃ entry ∈ program, entry.data.family = family ∧ query = entry.query := by
  change ∃ i, query = ((program.filter fun entry => entry.data.family == family).get i).query at member
  obtain ⟨i, equal⟩ := member
  have present := List.get_mem (program.filter fun entry => entry.data.family == family) i
  obtain ⟨present, selected⟩ := List.mem_filter.mp present
  exact ⟨_, present, by simpa using selected, equal⟩

theorem rv_mapped_query {Kind Target : Type} {p : Nat} (f : Kind → Target)
    (entry : RVProgramEntry Kind) : (entry.mapFamily f).query (p := p) = entry.query := rfl

/-- The native fetch query fixes both canonical PC limbs, for any family. -/
theorem rv_native_query_pc_word {Kind : Type} {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p}
    {entry : RVProgramEntry Kind}
    (equal : nativeDecoderQuery columns decoder w = entry.query) :
    (⟨(w columns.initialPC[0]).val, (w columns.initialPC[1]).val⟩ : Word) =
      Word.ofBitVec entry.pc := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[0]) equal
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[1]) equal
  change w columns.initialPC[0] = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
  change w columns.initialPC[1] = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
  exact word_of_pc_query hp low high

/-- A row's start PC is its program entry's PC, for any circuit layout. -/
theorem rv_query_pc {Kind ISA : Type} [CircuitLayout Kind] {p : Nat} (hp : limbBase < p)
    {row : Row p Kind} {entry : RVProgramEntry ISA}
    (equal : row.decoderQuery = entry.query) : row.start.word.toBitVec = entry.pc := by
  have word : row.start.word = Word.ofBitVec entry.pc := rv_native_query_pc_word hp equal
  rw [word, Word.ofBitVec_roundtrip]

/-- The same imported query fixes immediate limbs for every circuit family. -/
theorem rv_native_query_immediate_word {Kind : Type} {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p}
    {entry : RVProgramEntry Kind} (bound : entry.data.immediate.Bounded)
    (equal : nativeDecoderQuery columns decoder w = entry.query) :
    (⟨(w decoder.immediate[0]).val, (w decoder.immediate[1]).val⟩ : Word) =
      entry.data.immediate := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) equal
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) equal
  change w decoder.immediate[0] = (entry.data.immediate.lo : ZMod p) at low
  change w decoder.immediate[1] = (entry.data.immediate.hi : ZMod p) at high
  rw [low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 hp),
    ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]

/-- Canonical register indices from any family's imported nine-column query. -/
theorem rv_native_query_indices {Kind : Type} {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p}
    {entry : RVProgramEntry Kind}
    (equal : nativeDecoderQuery columns decoder w = entry.query) :
    (w decoder.rs1).val = entry.data.rs1.toNat ∧
    (w decoder.rs2).val = entry.data.rs2.toNat ∧
    (w decoder.rd).val = entry.data.rd.toNat := by
  have scalar {column : Nat} {index : BitVec 5}
      (same : w column = (index.toNat : ZMod p)) : (w column).val = index.toNat := by
    rw [same, ZMod.val_natCast_of_lt (lt_trans index.isLt (by dsimp [limbBase] at hp; omega))]
  exact ⟨scalar (congrArg (fun q : Vector (ZMod p) 9 => q[2]) equal),
    scalar (congrArg (fun q : Vector (ZMod p) 9 => q[3]) equal),
    scalar (congrArg (fun q : Vector (ZMod p) 9 => q[4]) equal)⟩

/-! ### Native metadata of ADD/SUB/ADDI/LUI/AUIPC and LW/SW (`Trace.rvDecoderFields`) -/

private theorem arithmetic_field_bounds (rs1 rs2 rd : BitVec 5) (bits : BitVec 32)
    {mask : Nat} (small : mask ≤ 4) :
    (arithmeticFields rs1 rs2 rd bits mask).immediate.Bounded ∧
      (arithmeticFields rs1 rs2 rd bits mask).mask ≤ 4 := by
  unfold arithmeticFields
  split
  · exact ⟨by simp [Word.Bounded, limbBase], by decide⟩
  · exact ⟨Word.ofBitVec_bound bits, small⟩

private theorem arithmetic_zero_fields (rs1 rs2 rd : BitVec 5) (bits : BitVec 32) (mask : Nat)
    (zero : (arithmeticFields rs1 rs2 rd bits mask).rd = 0) :
    arithmeticFields rs1 rs2 rd bits mask = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by
  unfold arithmeticFields at *
  split at zero <;> simp_all

private theorem arithmetic_family (rs1 rs2 rd : BitVec 5) (bits : BitVec 32) (mask : Nat) :
    (arithmeticFields rs1 rs2 rd bits mask).family = .addSub := by
  unfold arithmeticFields
  split <;> rfl

/-- Every successful projection has a canonical immediate and a mask of at most 4 (as `decoder_field_bounds`). -/
theorem rv_decoder_field_bounds {i : RV.Instr} {data : DecoderData}
    (fields : rvDecoderFields i = some data) : data.immediate.Bounded ∧ data.mask ≤ 4 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       first
         | exact arithmetic_field_bounds _ _ _ _ (by decide)
         | exact ⟨Word.ofBitVec_bound _, by dsimp; omega⟩)

/-- Arithmetic writes to x0 (including a discarded LW) are the zero-operand ADD row (as `decoder_zero_nop`). -/
theorem rv_decoder_zero_nop {i : RV.Instr} {data : DecoderData}
    (fields : rvDecoderFields i = some data) (family : data.family = .addSub)
    (zero : data.rd = 0) : data = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       first
         | exact arithmetic_zero_fields _ _ _ _ _ zero
         | cases family)

/-- A word-memory load never targets x0 (as `decoder_load_nonzero`). -/
theorem rv_decoder_load_nonzero {i : RV.Instr} {data : DecoderData}
    (fields : rvDecoderFields i = some data) (family : data.family = .wordMemory)
    (load : data.mask = 0) : data.rd ≠ 0 := by
  unfold rvDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       first
         | (have impossible : Family.addSub = .wordMemory := by
              simpa only [arithmetic_family] using family
            cases impossible)
         | (change 1 = 0 at load; cases load)
         | assumption)

/-- `DecoderRules` for a projection on `RV.Instr`: the metadata facts used by the x0 argument. -/
structure RVDecoderRules (projection : RV.Instr → Option DecoderData) : Prop where
  bounds : ∀ i data, projection i = some data → data.immediate.Bounded ∧ data.mask < 512
  zeroNop : ∀ i data, projection i = some data →
    data.family = .addSub → data.rd = 0 → data = ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩
  loadNonzero : ∀ i data, projection i = some data →
    data.family = .wordMemory → data.mask = 0 → data.rd ≠ 0

theorem rvStandardDecoderRules : RVDecoderRules rvDecoderFields where
  bounds _ _ fields := by
    have bound := rv_decoder_field_bounds fields
    exact ⟨bound.1, by omega⟩
  zeroNop _ _ := rv_decoder_zero_nop
  loadNonzero _ _ := rv_decoder_load_nonzero

/-- Registry selection retains a successful family projection (as `pooled_fields_cases`). -/
theorem rv_pooled_fields_cases {i : RV.Instr} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields i = some data) :
    (∃ d, rvDecoderFields i = some d ∧ data = d.mapFamily pooledArithmeticFamily) ∨
    (∃ d, JumpBranchSlt.rvDecoderFields i = some d ∧ data = d.mapFamily (fun _ => .jumpBranchSlt)) ∨
    (∃ d, MulDiv.rvDecoderFields i = some d ∧ data = d.mapFamily (fun _ => .mulDiv)) ∨
    (∃ d, ShiftBinop.rvDecoderFields i = some d ∧ data = d.mapFamily (fun _ => .shiftBinop)) ∨
    (∃ d, SubwordMemory.rvDecoderFields i = some d ∧ data = d.mapFamily (fun _ => .subwordMemory)) := by
  unfold rvPooledDecoderFields at fields
  cases a : rvDecoderFields i
  · cases b : JumpBranchSlt.rvDecoderFields i
    · cases c : MulDiv.rvDecoderFields i
      · cases d : ShiftBinop.rvDecoderFields i
        · cases e : SubwordMemory.rvDecoderFields i
          · simp [a, b, c, d, e] at fields
          · rw [a, b, c, d, e] at fields
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl, (Option.some.inj fields).symm⟩)))
        · rw [a, b, c, d] at fields
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, (Option.some.inj fields).symm⟩)))
      · rw [a, b, c] at fields
        exact Or.inr (Or.inr (Or.inl ⟨_, rfl, (Option.some.inj fields).symm⟩))
    · rw [a, b] at fields
      exact Or.inr (Or.inl ⟨_, rfl, (Option.some.inj fields).symm⟩)
  · rw [a] at fields
    exact Or.inl ⟨_, rfl, (Option.some.inj fields).symm⟩

end Airbender.Trace.Proofs
