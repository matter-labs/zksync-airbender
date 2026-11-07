import Airbender.Proofs.GKRProtocol.PackedSetupEquality
import Airbender.Proofs.GKRProtocol.BlockNormalization

namespace Airbender.Compiler.PackedSetupNormalization
open Airbender.Setup PackedSetupEquality
set_option warningAsError true

/- Equal recipes avoid expansion. Different recipes use the exact array test. -/
def arrayEqual (left right : ArrayCode) : Bool :=
  if left = right then true else decide (left.decode = right.decode)

theorem arrayEqual_eq (left right : ArrayCode) :
    arrayEqual left right = decide (left.decode = right.decode) := by
  unfold arrayEqual
  split_ifs with same
  · subst right; simp
  · rfl

def merge : BlockCode → BlockCode → Option BlockCode
  | .affine left first step, .affine right next other =>
      if step = other ∧ (first : Int) + step * left = next then
        some (.affine (left + right) first step)
      else none
  | .periodic left step values, .periodic right other next =>
      if step = 0 ∧ other = 0 ∧ arrayEqual values next = true then
        some (.periodic (left + right) 0 values)
      else none
  | _, _ => none

theorem merge_decode (left right : BlockCode) :
    (merge left right).map BlockCode.decode = mergeSetupBlocks left.decode right.decode := by
  cases left <;> cases right <;>
    simp only [merge, mergeSetupBlocks, arrayEqual_eq, decide_eq_true_eq]
  all_goals first | rfl | skip
  all_goals split <;> rfl

def prepend (block : BlockCode) : List BlockCode → List BlockCode
  | [] => [block]
  | next :: rest =>
      match merge block next with
      | none => block :: next :: rest
      | some joined => joined :: rest

def normalize : List BlockCode → List BlockCode
  | [] => []
  | block :: rest => prepend block (normalize rest)

theorem prepend_decode (block : BlockCode) (tail : List BlockCode) :
    (prepend block tail).map BlockCode.decode =
      prependNormalizedBlock block.decode (tail.map BlockCode.decode) := by
  cases tail with
  | nil => rfl
  | cons next rest =>
      have binding := merge_decode block next
      cases found : merge block next with
      | none =>
          rw [found] at binding
          simp only [Option.map_none] at binding
          simp only [prepend, found, List.map_cons, prependNormalizedBlock, ← binding]
      | some joined =>
          rw [found] at binding
          simp only [Option.map_some] at binding
          simp only [prepend, found, List.map_cons, prependNormalizedBlock, ← binding]

theorem normalize_decode (blocks : List BlockCode) :
    (normalize blocks).map BlockCode.decode = normalizeSetupBlocks (blocks.map BlockCode.decode) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      rw [normalize, prepend_decode, ih]
      rfl

structure Request where
  source : List BlockCode
  target : List BlockCode
  rows : Nat
  deriving DecidableEq

def requestCheck (request : Request) : Bool :=
  (if request.source = request.target then true
   else decide (normalize request.source = normalize request.target)) &&
    ((request.source.map BlockCode.length).sum == request.rows)

def check (requests : List Request) : Bool := requests.all requestCheck

def Fact (request : Request) : Prop :=
  normalizeSetupBlocks (request.source.map BlockCode.decode) =
    normalizeSetupBlocks (request.target.map BlockCode.decode) ∧
  ((request.source.map BlockCode.decode).map Block.length).sum = request.rows

theorem requestCheck_sound (request : Request) (checked : requestCheck request = true) : Fact request := by
  simp only [requestCheck, Bool.and_eq_true] at checked
  rcases checked with ⟨same, rows⟩
  constructor
  · rw [← normalize_decode, ← normalize_decode]
    have normalized : normalize request.source = normalize request.target := by
      split_ifs at same with equal
      · exact congrArg normalize equal
      · exact of_decide_eq_true same
    exact congrArg (List.map BlockCode.decode) normalized
  · simpa only [List.map_map, Function.comp_def, BlockCode.decode_length] using (beq_iff_eq.mp rows)

theorem check_sound (requests : List Request) (checked : check requests = true) :
    ∀ request ∈ requests, Fact request := by
  intro request member
  exact requestCheck_sound request (List.all_eq_true.mp checked request member)

theorem check_sound_at (requests : List Request) (checked : check requests = true)
    (index : Fin requests.length) : Fact (requests.get index) :=
  check_sound requests checked _ (List.get_mem requests index)

end Airbender.Compiler.PackedSetupNormalization
