module
public import Proven.Compiler.Proth120Native
public import Proven.UnifiedReduced.Proth120.RowWitness

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120.Witness
open Compiler.Proth120Native
set_option maxRecDepth 32768

noncomputable def physicalFor (w : Nat → F) (a : GKRAddress) : F :=
  w ((placements.find? (fun kv => kv.2 == a)).map Prod.fst |>.getD 0)

noncomputable abbrev nativePhysical := physicalFor (assignment .fma)

theorem arithmetic_of_checks (w : Nat → F)
    (equations : gates.all (fun g => decide (Gate.Holds nativeScalar (physicalFor w) g)) = true)
    (placed : placements.all (fun kv => decide (w kv.1 = physicalFor w kv.2)) = true) :
    NativeArithmetic (physicalFor w) w :=
  ⟨fun g hg => of_decide_eq_true (List.all_eq_true.mp equations g hg),
   fun kv hm => of_decide_eq_true (List.all_eq_true.mp placed kv hm)⟩

theorem nativeArithmetic : NativeArithmetic nativePhysical (assignment .fma) :=
  arithmetic_of_checks _ (by kernel_rfl) (by kernel_rfl)

def decoderVector : Vector F 9 := #v[0,0,1,2,3,0,0,0,64]

/-- The two public generic rows used by the FMA witness: the zero setup row and the
    decoded program row at PC 0, with the native discriminator appended. -/
def genericRows (xs : List F) : Prop :=
  xs = (Vector.replicate 10 (0 : F)).toList ∨ xs = decoderVector.toList ++ [46]

noncomputable def nativeRows : PublicLookupRows (tableWith (Trace.ROM.wordsRV initial)) (Decoded initial) where
  generic := genericRows
  pooled := by
    intro v member hz
    rcases member with eq | eq
    · obtain rfl := Vector.toList_inj.mp eq
      exact ⟨⟨0, by decide⟩, by kernel_rfl⟩
    · have hv := congrArg (fun xs : List F => xs[8]?) eq
      have hi : v.toList[8]? = some v[8] := List.getElem?_eq_getElem (by simp)
      rw [hi, hz] at hv
      exact False.elim ((by decide +kernel : ¬ (some (0 : F) = some 64)) hv)
  decoder := by
    intro v member
    rcases member with eq | eq
    · have hv := congrArg List.getLast? eq
      simp [Vector.toList_replicate] at hv
      exact False.elim ((by decide +kernel : (46 : F) ≠ 0) hv)
    · obtain rfl := Vector.toList_inj.mp (List.append_cancel_right eq)
      exact fma_inputs.decoded

noncomputable def queryCheck (physical : GKRAddress → F) (q : Query) : Bool :=
  (q.enable.map physical).getD 1 == 0 || (let xs := q.fields.map (value nativeScalar physical)
  match q.group, xs with
  | 0, _ => xs == (Vector.replicate 10 (0 : F)).toList || xs == decoderVector.toList ++ [46]
  | 1, [x] => x.val < 65536
  | 2, [x] => x.val < Trace.timestampBase
  | _, _ => false)

theorem matched_of_check (physical : GKRAddress → F)
    (h : nativeQueries.all (queryCheck physical) = true) : NativeLookupsMatched nativeRows.generic physical := by
  intro q hq enabled
  have valid := List.all_eq_true.mp h q hq
  simp only [queryCheck, Bool.or_eq_true, beq_iff_eq, enabled, false_or] at valid
  generalize q.fields.map (value nativeScalar physical) = xs at valid ⊢
  dsimp only at valid ⊢
  generalize q.group = group at valid ⊢
  split at valid
  · simpa [nativeRows, genericRows] using valid
  · exact ⟨⟨_, of_decide_eq_true valid⟩, congrArg (fun (y : F) => [y]) (ZMod.natCast_zmod_val _).symm⟩
  · exact ⟨⟨_, of_decide_eq_true valid⟩, congrArg (fun (y : F) => [y]) (ZMod.natCast_zmod_val _).symm⟩
  · cases valid

theorem nativeMatched : NativeLookupsMatched nativeRows.generic nativePhysical :=
  matched_of_check _ (by kernel_rfl)

end Airbender.UnifiedReduced.Proth120.Witness
