import Airbender.Proofs.GKRProtocol.PackedSetupAccess
import Airbender.Proofs.GKRProtocol.PackedSetupNormalization
import Airbender.Proofs.GKRProtocol.BlockSpans

namespace Airbender.Compiler.PackedSetupSpans
open Airbender.Setup PackedSetupEquality PackedSetupAccess PackedSetupNormalization
set_option warningAsError true

def finiteCheck (source target : BlockCode) (offset : Nat) : Bool :=
  decide (target.length ≤ 256) && (List.finRange target.length).all
    (fun index => blockGet source (offset + index.val) == blockGet target index.val)

theorem finiteCheck_sound (source target : BlockCode) (offset : Nat)
    (checked : finiteCheck source target offset = true) (index : Nat) (bounded : index < target.length) :
    source.decode.get? (offset + index) = target.decode.get? index := by
  simp only [finiteCheck, Bool.and_eq_true] at checked
  have same := beq_iff_eq.mp (List.all_eq_true.mp checked.2 ⟨index, bounded⟩ (List.mem_finRange _))
  simpa only [blockGet_decode] using same

def spanCheck (source target : BlockCode) (offset : Nat) : Bool :=
  if offset = 0 ∧ source = target then true
  else match source, target with
    | .affine left first step, .affine right next other =>
        if step = other ∧ offset + right ≤ left ∧ (first : Int) + step * offset = next
        then true else finiteCheck source target offset
    | .periodic left step values, .periodic right other next =>
        if step = 0 ∧ other = 0 ∧ arrayEqual values next = true ∧
            offset % values.length = 0 ∧ offset + right * next.length ≤ left * values.length
        then true else finiteCheck source target offset
    | _, _ => finiteCheck source target offset

theorem spanCheck_sound (source target : BlockCode) (offset : Nat)
    (checked : spanCheck source target offset = true) (index : Nat) (bounded : index < target.length) :
    source.decode.get? (offset + index) = target.decode.get? index := by
  unfold spanCheck at checked
  split_ifs at checked with identical
  · rcases identical with ⟨rfl, rfl⟩
    simp only [Nat.zero_add]
  · cases source <;> cases target
    all_goals dsimp only at checked
    all_goals try exact finiteCheck_sound _ _ _ checked index bounded
    case affine.affine left first step right next other =>
      split_ifs at checked with guard
      · rcases guard with ⟨rfl, fits, start⟩
        exact affine_block_span left right first next offset index step (by
          change index < right at bounded; omega) bounded start
      · exact finiteCheck_sound _ _ _ checked index bounded
    case periodic.periodic left step values right other next =>
      split_ifs at checked with guard
      · rcases guard with ⟨rfl, rfl, equal, aligned, fits⟩
        rw [arrayEqual_eq] at equal
        have arrays := of_decide_eq_true equal
        have lengths : values.length = next.length := by
          simpa only [ArrayCode.decode_length] using congrArg Array.size arrays
        change (Block.periodic left 0 values.decode).get? (offset + index) =
          (Block.periodic right 0 next.decode).get? index
        rw [← arrays]
        apply periodic_zero_block_span
        · rw [ArrayCode.decode_length]
          change index < right * next.length at bounded
          omega
        · rw [ArrayCode.decode_length, lengths]
          exact bounded
        · simpa only [ArrayCode.decode_length] using aligned
      · exact finiteCheck_sound _ _ _ checked index bounded

def followCheck (source : BlockCode) (offset : Nat) : List BlockCode → Bool
  | [] => true
  | target :: rest => spanCheck source target offset && followCheck source (offset + target.length) rest

theorem followCheck_sound (source : BlockCode) (offset : Nat) (targets : List BlockCode)
    (checked : followCheck source offset targets = true) :
    blockTargetsFollow source.decode offset (targets.map BlockCode.decode) := by
  induction targets generalizing offset with
  | nil => trivial
  | cons target rest ih =>
      simp only [followCheck, Bool.and_eq_true] at checked
      constructor
      · intro index bounded
        apply spanCheck_sound source target offset checked.1 index
        simpa only [BlockCode.decode_length] using bounded
      · simpa only [BlockCode.decode_length] using ih (offset + target.length) checked.2

structure Request where
  source : BlockCode
  targets : List BlockCode
  deriving DecidableEq

def requestCheck (request : Request) : Bool :=
  ((request.targets.map BlockCode.length).sum == request.source.length) &&
    followCheck request.source 0 request.targets

def check (requests : List Request) : Bool := requests.all requestCheck

def Fact (request : Request) : Prop :=
  ((request.targets.map BlockCode.decode).map Block.length).sum = request.source.decode.length ∧
  blockTargetsFollow request.source.decode 0 (request.targets.map BlockCode.decode)

theorem requestCheck_sound (request : Request) (checked : requestCheck request = true) : Fact request := by
  simp only [requestCheck, Bool.and_eq_true] at checked
  constructor
  · simpa only [List.map_map, Function.comp_def, BlockCode.decode_length] using beq_iff_eq.mp checked.1
  · exact followCheck_sound _ _ _ checked.2

theorem check_sound (requests : List Request) (checked : check requests = true) :
    ∀ request ∈ requests, Fact request := by
  intro request member
  exact requestCheck_sound request (List.all_eq_true.mp checked request member)

theorem check_sound_at (requests : List Request) (checked : check requests = true)
    (index : Fin requests.length) : Fact (requests.get index) :=
  check_sound requests checked _ (List.get_mem requests index)

theorem check_sound_bound_at (requests : List Request) (checked : check requests = true)
    (index : Fin requests.length) (source : Block) (targets : List Block)
    (source_binding : source = (requests.get index).source.decode)
    (targets_binding : targets = (requests.get index).targets.map BlockCode.decode) :
    (targets.map Block.length).sum = source.length ∧ blockTargetsFollow source 0 targets := by
  rw [source_binding, targets_binding]
  exact check_sound_at requests checked index

end Airbender.Compiler.PackedSetupSpans
