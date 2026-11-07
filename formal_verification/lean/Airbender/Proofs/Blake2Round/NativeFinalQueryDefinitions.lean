import Airbender.Proofs.Blake2Round.NativeFinalLayout

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

abbrev finalQuery := @NativeFinalLayout.query
abbrev finalColumn := @NativeFinalLayout.queryColumn

def acTemp {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) (part : Fin 6) : ZMod p :=
  NativeFinalLayout.temporary w (limb.castLE (by decide)) part
def bdIndex (limb : Fin 8) : Fin 16 := ⟨8 + limb.val, by omega⟩
def bdTemp {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) (part : Fin 6) : ZMod p :=
  NativeFinalLayout.temporary w (bdIndex limb) part

def acInitial {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  NativeFinalLayout.initial w (limb.castLE (by decide))
def acA {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  NativeFinalLayout.firstInput w (limb.castLE (by decide))
def acC {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  NativeFinalLayout.secondInput w (limb.castLE (by decide))
def bdInitial {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  NativeFinalLayout.initial w (bdIndex limb)
def bdB {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  NativeFinalLayout.firstInput w (bdIndex limb)
def bdD {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  NativeFinalLayout.secondInput w (bdIndex limb)

abbrev acLowC := @NativeFinalLayout.lowC
abbrev acLowA := @NativeFinalLayout.lowA
abbrev bdLowB := @NativeFinalLayout.lowB
abbrev bdLowD := @NativeFinalLayout.lowD

def bdHighB {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  (-3932160 : ZMod p) * (bdB w limb - bdLowB w limb)
def bdHighD {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  (-7864320 : ZMod p) * (bdD w limb - bdLowD w limb)

end Airbender.Blake2Round.Proofs
