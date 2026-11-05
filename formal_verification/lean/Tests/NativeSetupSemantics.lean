import Airbender.Proofs.BabyBear
import Airbender.Proofs.Trace.Program
import Airbender.Review.Helpers.Decoder.ImportedPooled
import Airbender.Review.Helpers.Decoder.ImportedProgram
import Airbender.Review.Circuits.WordMemory.Tables.Setup

namespace Airbender.Tests.NativeSetupSemantics
open Trace Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def firstEntry : ProgramEntry PooledFamily :=
  ⟨0, 19, .ITYPE (0, .Regidx 0, .Regidx 0, .ADDI),
    ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩

/-- The actual first imported word is decoded by the original Sail decoder. -/
theorem first_entry_is_original :
    selectedEntry pooledDecoderFields ⟨0, by decide⟩ = some firstEntry := by rfl

/-- A real imported decoder row admits its actual decoded instruction. -/
theorem accepted_decoder :
    addSubSetup.lookup (firstEntry.query (p := babyBearModulus)) := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  decide +kernel

/-- A real native ROM query retrieves the first independently imported word. -/
theorem accepted_rom :
    (ROM.importedTable (p := babyBearModulus)).Contains #[]
      #v[0, 19, 0, 0, 0, 0, 0, 0, 34] := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  decide +kernel

/-- Disabled native lookups retain the actual zero entry. -/
theorem accepted_disabled :
    (ROM.importedTable (p := babyBearModulus)).Contains #[]
      (Vector.replicate 9 0) := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  decide +kernel

private def absentQuery : Vector (ZMod babyBearModulus) 9 := #v[16, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem normalize_pc (packed : Vector Nat addSubSetup.width) :
    (addSubSetup.normalize packed)[0] = packed[0] := by
  simp only [PackedSetup.normalize, Vector.getElem_ofFn]
  change (packed.toArray[0]?).getD 0 = packed[0]
  simp only [Vector.getElem?_toArray,
    Vector.getElem?_eq_getElem (xs := packed) (i := 0) (by decide), Option.getD_some]

private theorem real_offset : addSubSetup.realRows.offset = 0 := rfl
private theorem padding_offset : addSubSetup.padding.offset = 0 := rfl
private theorem real_length : addSubSetup.realRows.length = 1048576 := rfl

private theorem real_pc_column : addSubDecoderData.columns[0] =
    (⟨#[.dense #[0, 4, babyBearModulus - 1, 12],
      .affine 1048572 (babyBearModulus - 1) 0]⟩ : Setup.Column) := rfl

private theorem padding_pc_column : addSubDecoderDataPadding.columns[0] =
    (⟨#[.affine 15728640 (babyBearModulus - 1) 0]⟩ : Setup.Column) := rfl

/-- The retained real and padding columns admit only these PC values. -/
private theorem decoder_pc_domain (index : Fin 16777216) :
    (addSubSetup.row index)[0] ∈ ([0, 4, 12, babyBearModulus - 1] : List Nat) := by
  unfold PackedSetup.row
  split_ifs with real
  · simp only [normalize_pc, Vector.getElem_map, real_offset, Nat.zero_add]
    change ((addSubDecoderData.columns[0].get? index.val).getD 0) ∈
      ([0, 4, 12, babyBearModulus - 1] : List Nat)
    by_cases short : index.val < 4
    · generalize eq : index.val = n at *
      interval_cases n <;>
        simp [real_pc_column, Setup.Column.get?, Setup.getFromBlocks,
          Setup.Block.length, Setup.Block.get?]
    · have bounded : index.val - 4 < 1048572 := by
        have extent : index.val < 1048576 := real
        omega
      have value : addSubDecoderData.columns[0].get? index.val = some (babyBearModulus - 1) := by
        rw [real_pc_column]
        change Setup.getFromBlocks [.dense #[0, 4, babyBearModulus - 1, 12],
          .affine 1048572 (babyBearModulus - 1) 0] index.val = _
        simp [Setup.getFromBlocks, Setup.Block.length, Setup.Block.get?, short, bounded]
      rw [value]
      simp
  · simp only [normalize_pc, Vector.getElem_map,
      padding_offset, real_length, Nat.zero_add]
    change ((addSubDecoderDataPadding.columns[0].get? (index.val - 1048576)).getD 0) ∈
      ([0, 4, 12, babyBearModulus - 1] : List Nat)
    have bounded : index.val - 1048576 < 15728640 := by
      have extent := index.isLt
      have outside : ¬ index.val < 1048576 := real
      omega
    have value : addSubDecoderDataPadding.columns[0].get? (index.val - 1048576) =
        some (babyBearModulus - 1) := by
      rw [padding_pc_column]
      change Setup.getFromBlocks [.affine 15728640 (babyBearModulus - 1) 0]
        (index.val - 1048576) = _
      simp [Setup.getFromBlocks, Setup.Block.length, Setup.Block.get?, bounded]
    rw [value]
    simp

/-- The imported complete domain cannot manufacture an instruction at an
    unsupported program slot from a fixed-table prefix or committed filler. -/
theorem unsupported_decoder_rejected : ¬ addSubSetup.lookup absentQuery := by
  rintro ⟨index, accepted⟩
  have noLeading : ¬ index.val < addSubSetup.offset := by change ¬ index.val < 0; omega
  rw [dif_neg noLeading] at accepted
  change activeQuery absentQuery = (addSubSetup.row index).map
    (fun n => (Setup.signedValue n : ZMod babyBearModulus)) at accepted
  have component := congrArg (fun q : Vector (ZMod babyBearModulus) 10 => q[0]) accepted
  simp only [Vector.getElem_map, activeQuery, Vector.getElem_ofFn] at component
  change (16 : ZMod babyBearModulus) =
    (Setup.signedValue ((addSubSetup.row index)[0]) : ZMod babyBearModulus) at component
  have domain := decoder_pc_domain index
  simp only [List.mem_cons, List.not_mem_nil, or_false] at domain
  rcases domain with equal | equal | equal | equal
  all_goals rw [equal] at component
  all_goals revert component
  all_goals decide +kernel

end Airbender.Tests.NativeSetupSemantics
