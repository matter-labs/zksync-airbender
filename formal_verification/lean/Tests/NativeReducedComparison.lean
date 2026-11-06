import Airbender.Review.Circuits.ReducedMachine.ComparisonTheorems
import Airbender.Review.Circuits.ReducedMachine.Tables.NativeConditionalTheorems
import Airbender.Review.Trace.Families.ReducedMachine.ComparisonResults
import Airbender.Review.Trace.Families.ReducedMachine.ComparisonValues
import Airbender.Proofs.JumpBranchSlt.NativeSetup

namespace Tests.NativeReducedComparison
open Airbender Arithmetic Trace ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def entries : Vector ComparisonProgramEntry 8 :=
  #v[⟨0,0x0020a1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLT),⟨⟨true,true⟩,1,2,3,⟨0,0⟩,67,2⟩⟩,
    ⟨0,0x0020b1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLTU),⟨⟨false,true⟩,1,2,3,⟨0,0⟩,67,3⟩⟩,
    ⟨0,0xfff0a193,.ITYPE (4095,.Regidx 1,.Regidx 3,.SLTI),⟨⟨true,false⟩,1,0,3,⟨65535,65535⟩,65,2⟩⟩,
    ⟨0,0xfff0b193,.ITYPE (4095,.Regidx 1,.Regidx 3,.SLTIU),⟨⟨false,false⟩,1,0,3,⟨65535,65535⟩,65,3⟩⟩,
    ⟨0,0x0020a033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SLT),⟨⟨true,true⟩,1,2,0,⟨0,0⟩,67,2⟩⟩,
    ⟨0,0x0020b033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SLTU),⟨⟨false,true⟩,1,2,0,⟨0,0⟩,67,3⟩⟩,
    ⟨0,0xfff0a013,.ITYPE (4095,.Regidx 1,.Regidx 0,.SLTI),⟨⟨true,false⟩,1,0,0,⟨65535,65535⟩,65,2⟩⟩,
    ⟨0,0xfff0b013,.ITYPE (4095,.Regidx 1,.Regidx 0,.SLTIU),⟨⟨false,false⟩,1,0,0,⟨65535,65535⟩,65,3⟩⟩]

/-- Actual reduced masks and every original ordinary/x0 constructor/sign extension. -/
theorem original_fields (i : Fin 8) : comparisonDecoderFields entries[i].instruction = some entries[i].data := by
  fin_cases i <;> rfl

/-- Every actual native resolver row participates at its original pool offset. -/
theorem actual_rows (i : Fin 128) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      ((conditionalRow i).map Nat.cast) := by
  refine ⟨⟨i.val+393345,by change i.val+393345 < 5771521; have := i.isLt; omega⟩,?_⟩
  change _ = (NativeFixed.rowNat ⟨i.val+393345,_⟩).map Nat.cast
  have h0 : ¬ i.val+393345 < 1 := by omega
  have h1 : ¬ i.val+393345 < 65537 := by omega
  have h2 : ¬ i.val+393345 < 131073 := by omega
  have h3 : ¬ i.val+393345 < 196609 := by omega
  have h4 : ¬ i.val+393345 < 262145 := by omega
  have h5 : ¬ i.val+393345 < 327681 := by omega
  have h6 : ¬ i.val+393345 < 393217 := by omega
  have h7 : ¬ i.val+393345 < 393345 := by omega
  have selected : i.val+393345 < 393473 := by have := i.isLt; omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  exact congrArg (fun v : Vector Nat 4 => v.map (Nat.cast : Nat → ZMod mersenne31Modulus))
    (NativeConditionalTableProofs.rows i).symm

/-- All128flag combinations use actual borrow-XOR-sign-difference semantics.
    Inconsistent tuples42/66 differ from the historical split resolver, without
    asserting those tuples occur in accepted architectural instructions. -/
theorem resolver_boundaries :
    conditionalRow ⟨2,by decide⟩ = #v[2,0,0,22] ∧
    conditionalRow ⟨10,by decide⟩ = #v[10,0,1,22] ∧
    conditionalRow ⟨42,by decide⟩ = #v[42,0,0,22] ∧
    conditionalRow ⟨66,by decide⟩ = #v[66,0,1,22] ∧
    conditionalRow ⟨127,by decide⟩ = #v[127,0,0,22] := by decide +kernel

/-- Independent signed/unsigned RV32 boundaries and negative-immediate meaning. -/
theorem reference_results :
    (ComparisonMode.mk true true).result 0x80000000 0 = 1 ∧
    (ComparisonMode.mk false true).result 0x80000000 0 = 0 ∧
    (ComparisonMode.mk true true).result 0x7fffffff 0xffffffff = 0 ∧
    (ComparisonMode.mk false true).result 0x7fffffff 0xffffffff = 1 ∧
    (ComparisonMode.mk true true).result 0xffffffff 0xffffffff = 0 ∧
    (ComparisonMode.mk false false).result 1 entries[3].data.immediate.toBitVec = 1 := by
  decide +kernel

/-- Actual resolver membership forbids a jump on a comparison key. -/
theorem wrong_jump_rejected {jump value : ZMod mersenne31Modulus}
    (member : (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[2,jump,value,22]) : jump ≠ 1 := by
  have actual := (NativeConditionalTableProofs.comparison member (Or.inl (by decide))).2.1
  rw [actual]
  decide +kernel

/-- The native table derives canonical keys, rejecting an oversized packed key. -/
theorem oversized_key_rejected {key jump value : ZMod mersenne31Modulus}
    (large : 128 ≤ key.val) :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[key,jump,value,22] := by
  intro member
  obtain ⟨i,same⟩ := NativeConditionalTableProofs.result _ member rfl
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [conditionalRow] using congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[0]) same
  rw [head,ZMod.val_natCast_of_lt (lt_trans i.isLt (by decide))] at large
  omega

/-- Encoded SLTIU at the original public byte address now uses the actual reduced
    projection; no old split native mask/table identity is transferred. -/
theorem original_public_slot :
    programSlotRunWith comparisonDecoderFields JumpBranchSlt.NativeSetup.before 8 =
      some (some (⟨8,0xfff0b013,.ITYPE (4095,.Regidx 1,.Regidx 0,.SLTIU),
        ⟨⟨false,false⟩,1,0,0,⟨65535,65535⟩,65,3⟩⟩ : ComparisonProgramEntry)) := by
  simp only [programSlotRunWith,
    show (Cell.ram (8 : BitVec 32)).read JumpBranchSlt.NativeSetup.before =
      .ok (0xfff0b013 : BitVec 32) JumpBranchSlt.NativeSetup.before from
        JumpBranchSlt.Proofs.native_fixture_words ⟨2,by decide⟩,bind,Option.bind]
  rfl

/-- Original raw funct3 is checked at the actual native ten-field query. -/
theorem corrupted_funct3_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = entries[0].query) : w 11 ≠ 3 := by
  have fields := NativeComparisonDecoderProofs.decoded_fields (original_fields 0) query
  rw [fields.funct3]
  decide +kernel

/-- Initialized comparison history rejects the unchecked oversized low source;
    no source bound or expected read is supplied to the public theorem. -/
theorem oversized_source_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ComparisonMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : comparisonDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells)
    (decoded : ComparisonDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (large : limbBase ≤ (row.assignment 35).val) : ¬ Accepted (fixedData trace) := by
  intro accepted
  have actual := (public_comparison_value_bounds image inputs accepted decoded).1 row present
    importedConstraintsMemoryPorts[0] (by cases row; rename_i family w; cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at actual
  exact Nat.not_le_of_gt actual.1 large

end Tests.NativeReducedComparison
