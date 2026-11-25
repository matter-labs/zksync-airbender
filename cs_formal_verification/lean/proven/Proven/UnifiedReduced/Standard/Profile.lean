module
public import Proven.CircuitField
public import Human.Helpers.Core.Word

@[expose] public section
namespace Airbender.UnifiedReduced.Standard

/-- The two checked-in unified CPU circuits. Their emitted equations can also be
    interpreted over an arbitrary prime `p`, as in the BabyBear row interface. -/
inductive Profile where | babyBear | proth120

def Profile.modulus : Profile → Nat
  | .babyBear => babyBearModulus
  | .proth120 => proth120Modulus

/-- ROM size in units of 65536 bytes, as used by the address-high-limb split. -/
def Profile.romLimbs : Profile → Nat
  | .babyBear => 64
  | .proth120 => 8

def Profile.byteInv (profile : Profile) {p : Nat} : ZMod p :=
  Int.cast (-(CircuitField.negInvPow profile.modulus 8 : Int))

def Profile.clockInv (profile : Profile) {p : Nat} : ZMod p :=
  Int.cast (-(CircuitField.negInvPow profile.modulus 19 : Int))

/-- Signed representative of the squared clock inverse in the original circuit field. -/
def Profile.clockSquare (profile : Profile) {p : Nat} : ZMod p :=
  let q := profile.modulus
  let n := (CircuitField.negInvPow q 19) ^ 2 % q
  Int.cast (if n ≤ q / 2 then (n : Int) else (n : Int) - q)

instance (profile : Profile) : CircuitField profile.modulus := match profile with
  | .babyBear => CircuitField.babyBear
  | .proth120 => CircuitField.proth120

theorem Profile.byteInv_correct (profile : Profile) : (profile.byteInv : ZMod profile.modulus) * 256 = 1 := by
  simpa only [Profile.byteInv, Int.cast_neg, Int.cast_natCast, show (2 : ZMod profile.modulus)^8 = 256 by norm_num] using
    (CircuitField.invPow_mul (p := profile.modulus) 8 (by decide))

theorem Profile.clockInv_correct (profile : Profile) : (profile.clockInv : ZMod profile.modulus) * 524288 = 1 := by
  simpa only [Profile.clockInv, Int.cast_neg, Int.cast_natCast, show (2 : ZMod profile.modulus)^19 = 524288 by norm_num] using
    (CircuitField.invPow_mul (p := profile.modulus) 19 (by decide))

theorem Profile.clockSquare_correct (profile : Profile) :
    (profile.clockInv : ZMod profile.modulus) * profile.clockInv = profile.clockSquare := by
  dsimp only [clockInv, clockSquare]
  split <;> simp [pow_two]

def Profile.choose (profile : Profile) {α : Type} (babyBear wrap : α) : α :=
  match profile with | .babyBear => babyBear | .proth120 => wrap

end Airbender.UnifiedReduced.Standard
