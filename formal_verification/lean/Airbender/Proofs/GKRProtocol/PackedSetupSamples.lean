import Airbender.Proofs.GKRProtocol.PackedSetupAccess
import Airbender.Proofs.Tables.AlignedConstants

namespace Airbender.Compiler.PackedSetupSamples
open Airbender.Setup PackedSetupEquality PackedSetupAccess
set_option warningAsError true

def getFromCodes : List BlockCode → Nat → Option Nat
  | [], _ => none
  | block :: tail, index =>
      if index < block.length then blockGet block index else getFromCodes tail (index - block.length)

theorem getFromCodes_decode (blocks : List BlockCode) (index : Nat) :
    getFromBlocks (blocks.map BlockCode.decode) index = getFromCodes blocks index := by
  induction blocks generalizing index with
  | nil => rfl
  | cons block tail ih =>
      simp only [List.map_cons, getFromBlocks, getFromCodes, BlockCode.decode_length,
        blockGet_decode, ih]

def alignedCheck : List BlockCode → Bool
  | [] => true
  | .affine length _ step :: tail =>
      step == 0 && length % 32768 == 0 && alignedCheck tail
  | _ => false

theorem alignedCheck_sound (blocks : List BlockCode) (checked : alignedCheck blocks = true) :
    Proofs.AlignedConstants (blocks.map BlockCode.decode) := by
  induction blocks with
  | nil => trivial
  | cons block tail ih =>
      cases block with
      | affine length first step =>
          simp only [alignedCheck, Bool.and_eq_true, beq_iff_eq] at checked
          exact ⟨checked.1.1, checked.1.2, ih checked.2⟩
      | dense values => simp [alignedCheck] at checked
      | periodic repetitions stride values => simp [alignedCheck] at checked

structure Request where
  blocks : List BlockCode
  count : Nat
  expected : Fin count → Nat

def check (requests : List Request) : Bool :=
  requests.all fun request => alignedCheck request.blocks &&
    (List.finRange request.count).all fun index =>
      getFromCodes request.blocks (index.val * 32768) == some (request.expected index)

def Fact (request : Request) : Prop :=
  Proofs.AlignedConstants (request.blocks.map BlockCode.decode) ∧
    ∀ index : Fin request.count,
      getFromBlocks (request.blocks.map BlockCode.decode) (index.val * 32768) =
        some (request.expected index)

theorem check_sound (requests : List Request) (checked : check requests = true)
    (request : Request) (member : request ∈ requests) : Fact request := by
  have row := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked request member)
  refine ⟨alignedCheck_sound request.blocks row.1, ?_⟩
  intro index
  rw [getFromCodes_decode]
  exact beq_iff_eq.mp (List.all_eq_true.mp row.2 index (List.mem_finRange index))

theorem check_sound_at (requests : List Request) (checked : check requests = true)
    (index : Fin requests.length) : Fact (requests.get index) :=
  check_sound requests checked _ (List.get_mem requests index)

theorem fact_bound (request : Request) (fact : Fact request) (blocks : List Block)
    (binding : blocks = request.blocks.map BlockCode.decode) :
    Proofs.AlignedConstants blocks ∧ ∀ index : Fin request.count,
      getFromBlocks blocks (index.val * 32768) = some (request.expected index) := by
  rw [binding]
  exact fact

end Airbender.Compiler.PackedSetupSamples
