import Human.SpecBlake
import Human.SpecExt4

/-! # The Fiat–Shamir check the program makes

The Blake2s (7 rounds) digest of the five input words is the transcript seed. The challenge `z` (an Ext4 element)
is made of its first four words, each as a BabyBear element (reduced mod `p`, as the field crate's
`from_raw_repr_with_reduction`; this program takes the reduced word as a canonical limb). The prover's claim `v`,
four more input words (also reduced), must be `poly4 z`; the program checks it and fails otherwise. -/

namespace Spec

/-- The challenge drawn from the transcript seed `d`. -/
noncomputable def challenge (d : Vector RV.Word 8) : E4 :=
  ofLimbs (d[0].toNat : F) (d[1].toNat : F) (d[2].toNat : F) (d[3].toNat : F)

/-- The prover's claim `v` is right for the input `w`: `v = poly4 z`, `z` the challenge from `w`'s digest. -/
def claimOK (w : Vector RV.Word 5) (v : Vector RV.Word 4) : Prop :=
  ofLimbs (v[0].toNat : F) (v[1].toNat : F) (v[2].toNat : F) (v[3].toNat : F) = poly4 (challenge (blake5 w))

end Spec
