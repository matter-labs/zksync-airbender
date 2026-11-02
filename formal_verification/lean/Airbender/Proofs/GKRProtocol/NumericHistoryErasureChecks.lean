import Airbender.Proofs.GKRProtocol.NumericQueryFrameChecks

namespace Airbender.Compiler.NumericHistoryErasureChecks
set_option warningAsError true
open NumericPolynomialChecks

structure Capture where
  coordinates : List Nat
  arithmetic : List (Data × Data)
  fields : List (Data × Data)

def erasedPair (coordinates : List (Fin n)) (polynomial : Polynomial n (ZMod p)) : Data × Data :=
  (encode polynomial, encode (substitute (erasurePolynomials coordinates) polynomial))

def arithmeticCheck (p : Nat) (coordinates : List Nat) (pair : Data × Data) : Bool :=
  NumericQueryFrameChecks.untouched coordinates pair.1 ||
    (NumericPolynomialChecks.equal p pair.2 [] || NumericPolynomialChecks.equal p pair.2 pair.1)

def fieldsCheck (p : Nat) (pair : Data × Data) : Bool :=
  NumericPolynomialChecks.equal p pair.2 pair.1

def check (p : Nat) (data : Capture) : Bool :=
  decide data.coordinates.Nodup && data.arithmetic.all (arithmeticCheck p data.coordinates) &&
    data.fields.all (fieldsCheck p)

def ofTyped (coordinates : List (Fin n)) (arithmetic fields : List (Polynomial n (ZMod p))) : Capture :=
  ⟨coordinates.map Fin.val, arithmetic.map (erasedPair coordinates), fields.map (erasedPair coordinates)⟩

def numericErasure (p : Nat) (coordinates : List Nat) (wire : Nat) : Data :=
  if coordinates.contains wire then [(0, [])] else [(1 % p, [wire])]

theorem numeric_erasure (coordinates : List (Fin n)) (wire : Fin n) :
    numericErasure p (coordinates.map Fin.val) wire.val =
      encode (erasurePolynomials coordinates wire : Polynomial n (ZMod p)) := by
  simp only [numericErasure, NumericQueryFrameChecks.contains_val, erasurePolynomials]
  split <;> simp_all [encode, constant, atom, ZMod.val_one_eq_one_mod]

def fastErasedPair (coordinates : List (Fin n)) (polynomial : Polynomial n (ZMod p)) : Data × Data :=
  (encode polynomial, NumericPolynomialChecks.substitute p
    (numericErasure p (coordinates.map Fin.val)) (encode polynomial))

theorem fastErasedPair_eq (coordinates : List (Fin n)) (polynomial : Polynomial n (ZMod p)) :
    fastErasedPair coordinates polynomial = erasedPair coordinates polynomial := by
  unfold fastErasedPair erasedPair
  rw [NumericPolynomialChecks.encode_substitute _ _ (numeric_erasure coordinates) polynomial]

def ofTypedFast (coordinates : List (Fin n)) (arithmetic fields : List (Polynomial n (ZMod p))) : Capture :=
  ⟨coordinates.map Fin.val, arithmetic.map (fastErasedPair coordinates), fields.map (fastErasedPair coordinates)⟩

theorem ofTypedFast_eq (coordinates : List (Fin n)) (arithmetic fields : List (Polynomial n (ZMod p))) :
    ofTypedFast coordinates arithmetic fields = ofTyped coordinates arithmetic fields := by
  have same : fastErasedPair coordinates = erasedPair (p := p) coordinates :=
    funext (fastErasedPair_eq coordinates)
  simp only [ofTypedFast, ofTyped, same]

theorem clock_inverse : (524288 : Source.BaseField)⁻¹ = 2013262081 := by
  have nonzero : (524288 : Source.BaseField) ≠ 0 := by decide +kernel
  have product : (524288 : Source.BaseField) * 2013262081 = 1 := by decide +kernel
  apply mul_left_cancel₀ nonzero
  rw [mul_inv_cancel₀ nonzero]
  exact product.symm

theorem clock_inverse_val : ((524288 : Source.BaseField)⁻¹).val = 2013262081 := by
  rw [clock_inverse]
  decide +kernel

def numericClockCarry (initial final : Source.MemoryWord) : Source.HelperField :=
  .scale 2013262081
    (.add (.add (.memory initial.low) (.memory (.constant 4))) (.neg (.memory final.low)))

def numericClockAssertions : Option (Source.MemoryWord × Source.MemoryWord) → List Source.HelperAssertion
  | none => []
  | some (initial, final) =>
      [.boolean (numericClockCarry initial final),
       .zero (.add (.add (.memory final.high) (.neg (.memory initial.high))) (.neg (numericClockCarry initial final)))]

theorem numericClockAssertions_eq (clock : Option (Source.MemoryWord × Source.MemoryWord)) :
    numericClockAssertions clock = Source.clockAssertionsFor clock := by
  cases clock with
  | none => rfl
  | some pair =>
      simp only [numericClockAssertions, Source.clockAssertionsFor, Source.clockAssertions,
        numericClockCarry, Source.clockCarry, clock_inverse_val]

def ofSource (coordinates : List (Fin n)) (originals : List (Expression n Source.BaseField))
    (clock : Option (Source.MemoryWord × Source.MemoryWord)) (placement : Source.HelperPlacement n)
    (fields : List (Polynomial n Source.BaseField)) : Capture :=
  ofTypedFast coordinates (originals.map Expression.polynomial ++
    (numericClockAssertions clock).map (Source.HelperAssertion.polynomial placement)) fields

theorem ofSource_eq (coordinates : List (Fin n)) (originals : List (Expression n Source.BaseField))
    (clock : Option (Source.MemoryWord × Source.MemoryWord)) (placement : Source.HelperPlacement n)
    (fields : List (Polynomial n Source.BaseField)) :
    ofSource coordinates originals clock placement fields =
      ofTyped coordinates (originals.map Expression.polynomial ++
        (Source.clockAssertionsFor clock).map (Source.HelperAssertion.polynomial placement)) fields := by
  unfold ofSource
  rw [numericClockAssertions_eq]
  exact ofTypedFast_eq coordinates _ fields

theorem encoded_nil (n p : Nat) : encode ([] : Polynomial n (ZMod p)) = [] := rfl

theorem arithmetic_encode [NeZero p] (coordinates : List (Fin n)) (polynomial : Polynomial n (ZMod p)) :
    arithmeticCheck p (coordinates.map Fin.val) (erasedPair coordinates polynomial) =
      (erasureUntouched coordinates polynomial ||
        (Airbender.Compiler.equal (substitute (erasurePolynomials coordinates) polynomial) [] ||
          Airbender.Compiler.equal (substitute (erasurePolynomials coordinates) polynomial) polynomial)) := by
  simp only [arithmeticCheck, erasedPair, NumericQueryFrameChecks.untouched_encode,
    ← encoded_nil n p, NumericPolynomialChecks.equal_encode]

theorem fields_encode [NeZero p] (coordinates : List (Fin n)) (polynomial : Polynomial n (ZMod p)) :
    fieldsCheck p (erasedPair coordinates polynomial) =
      Airbender.Compiler.equal (substitute (erasurePolynomials coordinates) polynomial) polynomial := by
  simp only [fieldsCheck, erasedPair, NumericPolynomialChecks.equal_encode]

theorem check_sound [NeZero p] (data : Capture) (coordinates : List (Fin n))
    (arithmetic fields : List (Polynomial n (ZMod p)))
    (binding : data = ofTyped coordinates arithmetic fields) (checked : check p data = true) :
    coordinates.Nodup ∧ erasureCheck coordinates arithmetic = true ∧
      fields.all (fun polynomial => Airbender.Compiler.equal (substitute (erasurePolynomials coordinates) polynomial) polynomial) = true := by
  rw [binding] at checked
  simp only [check, ofTyped, Bool.and_eq_true] at checked
  refine ⟨(of_decide_eq_true checked.1.1).of_map, ?_, ?_⟩
  · simpa only [List.all_map, Function.comp_def, arithmetic_encode, erasureCheck] using checked.1.2
  · simpa only [List.all_map, Function.comp_def, fields_encode] using checked.2

end Airbender.Compiler.NumericHistoryErasureChecks
