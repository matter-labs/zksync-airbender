import Airbender.Review.Circuits.JumpBranchSlt.Theorems
import Tests.JumpPC

namespace Tests.JumpDecoder
open Airbender Trace Verification
open Reference.RiscV.Sail

open JumpBranchSlt.NativeSetup

theorem public_words (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before = .ok words[i.val] before :=
  JumpBranchSlt.Proofs.native_fixture_words i

theorem public_image : JumpBranchSlt.sparseDecoderSetupImage before 3 20 = some setup :=
  JumpBranchSlt.Proofs.native_fixture_image

/-- Negative JAL retains raw encoded funct3 seven, unlike the source v3 profile. -/
theorem raw_jal_funct3 : JumpBranchSlt.decoderFields jalEntry.instruction = some jalEntry.data := rfl

theorem comparisons_to_x0 :
    JumpBranchSlt.decoderFields (.RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .SLT)) =
      some ⟨(), 1, 2, 0, ⟨0,0⟩, 4, 2⟩ ∧
    JumpBranchSlt.decoderFields sltiEntry.instruction = some sltiEntry.data := by
  exact ⟨rfl, rfl⟩

theorem unsigned_and_jalr_x0 :
    JumpBranchSlt.decoderFields (.RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .SLTU)) =
      some ⟨(), 1, 2, 0, ⟨0,0⟩, 4, 3⟩ ∧
    JumpBranchSlt.decoderFields (.ITYPE (4095, .Regidx 1, .Regidx 0, .SLTI)) =
      some ⟨(), 1, 0, 0, ⟨65535,65535⟩, 8, 2⟩ ∧
    JumpBranchSlt.decoderFields (.JALR (4095, .Regidx 1, .Regidx 0)) =
      some ⟨(), 1, 0, 0, ⟨65535,65535⟩, 2, 0⟩ := by
  exact ⟨rfl, rfl, rfl⟩

theorem branch_masks (op : SailRV32.bop) :
    JumpBranchSlt.decoderFields (.BTYPE (8190, .Regidx 2, .Regidx 1, op)) =
      some ⟨(), 1, 2, 0, ⟨65534,65535⟩, 16, JumpBranchSlt.Branch.funct3 op⟩ := by
  cases op <;> rfl

theorem hole_and_tail :
    setup.row (p := mersenne31Modulus) ⟨1, by decide⟩ = Vector.replicate 10 (-1) ∧
    setup.row (p := mersenne31Modulus) ⟨1048575, by decide⟩ = Vector.replicate 10 (-1) := by
  decide +kernel

/-- The public JAL tag changes the unconditional control lookup result, while
    preserving the same canonical PC target, actual link write and native clocks. -/
def assignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 11 then 7 else if i = 35 then 1 else JumpPC.negativeJal i

theorem native_constraints :
    FlatOperation.ConstraintsHoldFlat (environment assignment) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, JumpPC.negativeJal, JumpControl.assignment]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
      jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      assignment, JumpPC.negativeJal, JumpControl.assignment]
    solve
    | refine ⟨⟨7, by decide⟩, ?_⟩
      norm_num [conditionalControlRow, controlFlag]
    | refine ⟨⟨65532, by decide⟩, ?_⟩
      norm_num [jumpCleanupRow]

theorem public_membership : setup.table.Contains #[] (JumpBranchSlt.decoderQuery assignment) := by
  exact ⟨⟨0, by decide⟩, by decide +kernel⟩

theorem public_decoding : JumpBranchSlt.Fetched assignment before ∧
    (assignment 13).val < 65536 ∧ (assignment 14).val < 65536 :=
  JumpBranchSlt.native_public_decoding public_image native_constraints public_membership

theorem public_inputs :
    (⟨(assignment 0).val, (assignment 1).val⟩ : Arithmetic.Word).Bounded ∧
    (assignment 0).val % 4 = 0 ∧
    (⟨(assignment 9).val, (assignment 10).val⟩ : Arithmetic.Word).Bounded ∧
    assignment 8 = if (assignment 7).val = 0 then 1 else 0 :=
  JumpBranchSlt.Proofs.decoded_inputs (by decide) public_image native_constraints public_membership

/-- The old local tag-zero witness still satisfies native constraints, but its
    query is excluded by the actual public-byte construction. -/
theorem wrong_jal_tag_rejected :
    ¬setup.table.Contains #[] (JumpBranchSlt.decoderQuery JumpPC.negativeJal) := by
  intro member
  obtain ⟨entry, present, same⟩ := JumpBranchSlt.Proofs.decoder_member
    (by decide) JumpPC.negative_jal_constraints member
  simp only [setup, SparseDecoderSetup.program, List.filterMap_cons, List.filterMap_nil,
    id_eq, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  all_goals
    have tag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[8]) same
    norm_num [JumpBranchSlt.decoderQuery, nativeDecoderQuery,
      JumpBranchSlt.importedConstraintsDecoderColumns, ProgramEntry.query,
      jalEntry, sltiEntry, JumpPC.negativeJal, JumpControl.assignment] at tag
    first
    | exact (by decide : (0 : ZMod mersenne31Modulus) ≠ 7) tag
    | exact (by decide : (0 : ZMod mersenne31Modulus) ≠ 3) tag

theorem insufficient_capacity : JumpBranchSlt.sparseDecoderSetupImage before 3 1 = none := rfl

theorem discarded_jal :
    JumpBranchSlt.decoderFields (.JAL (0x1ffffc, .Regidx 0)) =
      some ⟨(), 0, 0, 0, ⟨65532,65535⟩, 1, 7⟩ := rfl

/-- The malformed PC variant now retains the actual public decoder fields. -/
def noncanonical (i : Nat) : ZMod mersenne31Modulus :=
  if i = 14 ∨ i = 43 then -1 else if i = 44 then 1 else assignment i

theorem noncanonical_public_membership :
    setup.table.Contains #[] (JumpBranchSlt.decoderQuery noncanonical) := by
  have same : JumpBranchSlt.decoderQuery noncanonical = JumpBranchSlt.decoderQuery assignment := rfl
  rw [same]
  exact public_membership

theorem noncanonical_polynomials :
    ∀ equation ∈ FlatOperation.constraints JumpBranchSlt.importedConstraints,
      equation.eval (environment noncanonical) = 0 := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.constraints, Expression.eval,
    environment, noncanonical, assignment, JumpPC.negativeJal, JumpControl.assignment]
  decide

theorem noncanonical_native_rejected :
    ¬FlatOperation.ConstraintsHoldFlat (environment noncanonical) JumpBranchSlt.importedConstraints := by
  intro holds
  have high := JumpBranchSlt.Proofs.candidate_high_bound holds
  change (-1 : ZMod mersenne31Modulus).val < 65536 at high
  exact (by decide : ¬(-1 : ZMod mersenne31Modulus).val < 65536) high

set_option maxRecDepth 32768 in
theorem missing_byte_rejected : JumpBranchSlt.sparseDecoderSetupImage
    { before with mem := before.mem.erase 0 } 3 20 = none := by
  cbv

end Tests.JumpDecoder
