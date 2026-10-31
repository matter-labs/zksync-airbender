import Airbender.Proofs.Tables.PackedPayload
import Airbender.Proofs.Tables.PackedRunColumn
import Airbender.Proofs.Tables.PackedWindows

namespace Airbender.Setup.Proofs.PackedBlockCertificate
open PackedColumn PackedRun PackedRunColumn PackedPayload
set_option warningAsError true

theorem decode_length (block : PackedBlock) : block.decode.length = block.length := by
  cases block <;> simp [PackedBlock.decode, PackedBlock.length, Block.length, packedArray]

theorem input_length (block : PackedBlock) (data : Setup.PackedRunInput)
    (encoded : block.input = some data) : block.length = data.length := by
  cases block with
  | affine length first stride =>
    cases stride <;> simp only [PackedBlock.input, Option.some.injEq] at encoded
    · subst data; simp [PackedBlock.length, PackedRunInput.length]
    · contradiction
  | dense length payload =>
    simp only [PackedBlock.input, Option.some.injEq] at encoded
    subst data
    simp [PackedBlock.length, PackedRunInput.length]
  | periodic count stride period payload =>
    cases stride <;> simp only [PackedBlock.input, Option.some.injEq] at encoded
    · subst data; rfl
    · contradiction

theorem input_raw (block : PackedBlock) (data : Setup.PackedRunInput)
    (encoded : block.input = some data) (valid : data.valid = true) :
    ofBlock block.decode = some data.asRun := by
  cases block with
  | affine length first stride =>
    cases stride with
    | negSucc stride => simp [PackedBlock.input] at encoded
    | ofNat stride =>
      simp only [PackedBlock.input, Option.some.injEq] at encoded
      subst data
      have bound : first < 256 := by
        simp only [PackedRunInput.valid, Bool.and_eq_true, decide_eq_true_eq,
          bytePower_eq, Nat.pow_one] at valid
        exact valid.1
      have stored : packedArray 1 first = #[first] := by
        apply Array.ext (by simp [packedArray])
        intro index leftBound rightBound
        have zero : index = 0 := by simpa [packedArray] using leftBound
        subst index
        simp [packedArray, packedByte, Nat.mod_eq_of_lt bound]
      simp only [PackedBlock.decode, ofBlock, PackedRunInput.asRun, stored]
  | dense length payload =>
    simp only [PackedBlock.input, Option.some.injEq] at encoded
    subst data
    rfl
  | periodic count stride period payload =>
    cases stride with
    | negSucc stride => simp [PackedBlock.input] at encoded
    | ofNat stride =>
      simp only [PackedBlock.input, Option.some.injEq] at encoded
      subst data
      rfl

def checkBlock (origin : Nat) (block : PackedBlock) : Bool :=
  match block.input with
  | none => false
  | some data => PackedWindows.legal origin data.length && data.valid &&
      data.packed == PackedWindows.span origin data.length

/-- The checker reads only numeric block metadata and packed payloads. -/
def check (origin : Nat) (blocks : List PackedBlock) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun block _ tail position =>
      match position with
      | 0 => checkBlock 0 block && tail block.length
      | next + 1 => checkBlock (next + 1) block && tail (next + 1 + block.length)) blocks) origin

private theorem check_cons (origin : Nat) (block : PackedBlock) (rest : List PackedBlock) :
    check origin (block :: rest) = (checkBlock origin block && check (origin + block.length) rest) := by
  cases origin with
  | zero => simp only [check, Nat.zero_add]
  | succ origin => rfl

theorem checkBlock_sound (origin : Nat) (block : PackedBlock)
    (checked : checkBlock origin block = true) (index : Nat) (within : index < block.decode.length) :
    block.decode.get? index = some ((origin + index) / 256 &&& (origin + index) % 256) := by
  cases encoded : block.input with
  | none => simp [checkBlock, encoded] at checked
  | some data =>
    simp only [checkBlock, encoded, Bool.and_eq_true, beq_iff_eq] at checked
    have raw := ofBlock_sound block.decode data.asRun (input_raw block data encoded checked.1.2)
    have withinRun : index < data.asRun.length := raw.1 ▸ within
    have withinInput : index < data.length := by rwa [run_length] at withinRun
    have extracted := packedArithmetic_byte data.asRun (valid_sound data checked.1.2) index withinRun
    rw [← packed_sound data checked.1.2, checked.2,
      PackedWindows.span_byte origin data.length index checked.1.1 withinInput] at extracted
    exact (raw.2 index within).trans (congrArg some extracted.symm)

/-- A single packed certificate proves the original source block equations. -/
theorem check_sound (origin : Nat) (blocks : List PackedBlock)
    (checked : check origin blocks = true) :
    checkBlocks (fun index => index / 256 &&& index % 256) origin (blocks.map PackedBlock.decode) = true := by
  induction blocks generalizing origin with
  | nil => rfl
  | cons block rest ih =>
    simp only [check_cons, Bool.and_eq_true] at checked
    rw [List.map_cons, checkBlocks_cons_iff]
    constructor
    · intro index
      exact checkBlock_sound origin block checked.1 index.val index.isLt
    · rw [decode_length]
      exact ih _ checked.2

end Airbender.Setup.Proofs.PackedBlockCertificate
