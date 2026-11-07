import Airbender.Review.Circuits.Blake2Worker.QueryArtifact
import Airbender.Review.Circuits.Blake2Worker.NativeArtifact
import Airbender.Review.Circuits.Blake2Worker.Tables

namespace Airbender.Blake2Worker.Native
open Verification QueryArtifact

/-- Native fixed-query order: eight18-query groups,32 extended-control queries,
    then32 finalization queries. This reference supplies no witness answers. -/
def fixedKind (slot : Fin 208) : Fixed.Kind :=
  if slot.val < 144 then
    match slot.val % 18 with
    | 4 | 7 => .three
    | 6 | 9 => .four
    | 5 | 8 | 15 | 17 => .nine
    | 14 | 16 => .seven
    | _ => .byte
  else if slot.val < 176 then
    if slot.val % 2 = 0 then .seven else .nine
  else match slot.val % 4 with
    | 0 => .nine
    | 1 => .seven
    | _ => .byte

def fixedExpressions {p : Nat} [Fact p.Prime] (slot : Fin 208) : Vector (Expression (ZMod p)) 4 :=
  if h : slot.val < 8 then queryFixed0.get ⟨slot.val,h⟩ else
  if h : slot.val < 72 then queryFixed1.get ⟨slot.val-8,by omega⟩ else
  if h : slot.val < 136 then queryFixed2.get ⟨slot.val-72,by omega⟩ else
  if h : slot.val < 200 then queryFixed3.get ⟨slot.val-136,by omega⟩ else
  queryFixed4.get ⟨slot.val-200,by have := slot.isLt; omega⟩

def fixedQuery (w : Nat → ZMod mersenne31Modulus) (slot : Fin 208) : Vector (ZMod mersenne31Modulus) 4 :=
  (fixedExpressions slot).map (Expression.eval (environment w))

def clockExpression {p : Nat} [Fact p.Prime] (slot : Fin 86) : Expression (ZMod p) :=
  if h : slot.val < 30 then queryClocks0.get ⟨slot.val,h⟩ else
  queryClocks1.get ⟨slot.val-30,by have := slot.isLt; omega⟩

/-- The ranges apply to the actual compiled scaled-pointer and timestamp-difference
    expressions. They are not bounds on raw old or processing timestamps. -/
structure LookupEffects (w : Nat → ZMod mersenne31Modulus) : Prop where
  scalars : ∀ slot : Fin 2, ((queryScalars[slot]).eval (environment w)).val < 65536
  clocks : ∀ slot : Fin 86, ((clockExpression slot).eval (environment w)).val < 524288
  fixedTags : ∀ slot : Fin 208, (fixedQuery w slot)[3] = ((fixedKind slot).tag : ZMod mersenne31Modulus)
  leftBounds : ∀ slot : Fin 208, (fixedQuery w slot)[0].val < (fixedKind slot).bound
  rightBounds : ∀ slot : Fin 208, (fixedQuery w slot)[1].val < (fixedKind slot).bound
  outputBounds : ∀ slot : Fin 208, (fixedQuery w slot)[2].val < (fixedKind slot).bound
  results : ∀ slot : Fin 208, (fixedQuery w slot)[2].val = (fixedQuery w slot)[0].val ^^^ (fixedQuery w slot)[1].val

end Airbender.Blake2Worker.Native
