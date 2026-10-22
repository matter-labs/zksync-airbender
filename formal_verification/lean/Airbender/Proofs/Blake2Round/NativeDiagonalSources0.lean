import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2Round.NativeLayout
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.Ring

namespace Airbender.Blake2Round.Proofs.NativeDiagonalView0
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def source0 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 404)],
      Arithmetic.linearExpression (0) [(1, 416)],
      Arithmetic.linearExpression (0) [(1, 417)],
      Arithmetic.linearExpression (0) [(1, 420)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source0_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (0 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source0 (p := p)) := rfl

def source0Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 404, w 416, w 417, w 420, 0, 55]

theorem source0_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source0.map (Expression.eval (Verification.environment w)) = source0Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source0, source0Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source1 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 407)],
      Arithmetic.linearExpression (0) [(-7864320, 155), (-7864320, 171), (-7864320, 224), (-7864320, 226), (-7864320, 240), (-256, 257), (-1006632960, 277), (-7864320, 278), (-256, 281), (-7864320, 332), (2, 335), (7864320, 416), (-256, 417)],
      Arithmetic.linearExpression (0) [(1, 421)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source1_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (1 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source1 (p := p)) := rfl

def source1Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 407, -7864320 * w 155 - 7864320 * w 171 - 7864320 * w 224 - 7864320 * w 226 - 7864320 * w 240 - 256 * w 257 - 1006632960 * w 277 - 7864320 * w 278 - 256 * w 281 - 7864320 * w 332 + 2 * w 335 + 7864320 * w 416 - 256 * w 417, w 421, 0, 0, 4]

theorem source1_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source1.map (Expression.eval (Verification.environment w)) = source1Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source1, source1Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source2 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 405)],
      Arithmetic.linearExpression (0) [(1, 418)],
      Arithmetic.linearExpression (0) [(1, 419)],
      Arithmetic.linearExpression (0) [(1, 422)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source2_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (2 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source2 (p := p)) := rfl

def source2Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 405, w 418, w 419, w 422, 0, 55]

theorem source2_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source2.map (Expression.eval (Verification.environment w)) = source2Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source2, source2Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source3 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 406)],
      Arithmetic.linearExpression (0) [(-7864320, 157), (-7864320, 173), (-7864320, 225), (-7864320, 227), (-7864320, 241), (-7864320, 257), (-256, 259), (-1006632960, 276), (-7864320, 279), (-7864320, 281), (-256, 283), (-7864320, 333), (2, 334), (-7864320, 417), (7864320, 418), (-256, 419)],
      Arithmetic.linearExpression (0) [(1, 423)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source3_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (3 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source3 (p := p)) := rfl

def source3Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 406, -7864320 * w 157 - 7864320 * w 173 - 7864320 * w 225 - 7864320 * w 227 - 7864320 * w 241 - 7864320 * w 257 - 256 * w 259 - 1006632960 * w 276 - 7864320 * w 279 - 7864320 * w 281 - 256 * w 283 - 7864320 * w 333 + 2 * w 334 - 7864320 * w 417 + 7864320 * w 418 - 256 * w 419, w 423, 0, 0, 4]

theorem source3_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source3.map (Expression.eval (Verification.environment w)) = source3Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source3, source3Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source4 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 431)],
      Arithmetic.linearExpression (0) [(1, 425)],
      Arithmetic.linearExpression (0) [(1, 434)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source4_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (4 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source4 (p := p)) := rfl

def source4Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 431, w 425, w 434, 0, 0, 20]

theorem source4_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source4.map (Expression.eval (Verification.environment w)) = source4Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source4, source4Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source5 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 433)],
      Arithmetic.linearExpression (0) [(1, 428)],
      Arithmetic.linearExpression (0) [(1, 435)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source5_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (5 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source5 (p := p)) := rfl

def source5Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 433, w 428, w 435, 0, 0, 20]

theorem source5_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source5.map (Expression.eval (Verification.environment w)) = source5Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source5, source5Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source6 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 332), (-251658240, 335), (491520, 430), (3932160, 431)],
      Arithmetic.linearExpression (0) [(1, 432)],
      Arithmetic.linearExpression (0) [(-491520, 190), (-491520, 344), (-125829120, 345), (-16, 348), (-491520, 364), (-125829120, 367), (-16, 369), (-491520, 422), (-125829120, 423), (491520, 424), (3932160, 425), (-16, 426)],
      Arithmetic.linearExpression (0) [(1, 427)],
      Arithmetic.linearExpression (0) [(1, 436)],
      Arithmetic.linearExpression (57) []]

theorem source6_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source6 (p := p)) := rfl

def source6Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 332 - 251658240 * w 335 + 491520 * w 430 + 3932160 * w 431, w 432, -491520 * w 190 - 491520 * w 344 - 125829120 * w 345 - 16 * w 348 - 491520 * w 364 - 125829120 * w 367 - 16 * w 369 - 491520 * w 422 - 125829120 * w 423 + 491520 * w 424 + 3932160 * w 425 - 16 * w 426, w 427, w 436, 57]

theorem source6_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source6.map (Expression.eval (Verification.environment w)) = source6Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source6, source6Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source7 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 333), (-251658240, 334), (491520, 432), (3932160, 433)],
      Arithmetic.linearExpression (0) [(1, 430)],
      Arithmetic.linearExpression (0) [(-491520, 191), (-491520, 342), (-125829120, 343), (-491520, 348), (-16, 351), (-491520, 365), (-125829120, 366), (-491520, 369), (-16, 371), (-491520, 420), (-125829120, 421), (-491520, 426), (491520, 427), (3932160, 428), (-16, 429)],
      Arithmetic.linearExpression (0) [(1, 424)],
      Arithmetic.linearExpression (0) [(1, 437)],
      Arithmetic.linearExpression (57) []]

theorem source7_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (7 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source7 (p := p)) := rfl

def source7Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 333 - 251658240 * w 334 + 491520 * w 432 + 3932160 * w 433, w 430, -491520 * w 191 - 491520 * w 342 - 125829120 * w 343 - 491520 * w 348 - 16 * w 351 - 491520 * w 365 - 125829120 * w 366 - 491520 * w 369 - 16 * w 371 - 491520 * w 420 - 125829120 * w 421 - 491520 * w 426 + 491520 * w 427 + 3932160 * w 428 - 16 * w 429, w 424, w 437, 57]

theorem source7_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source7.map (Expression.eval (Verification.environment w)) = source7Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source7, source7Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source8 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 423)],
      Arithmetic.linearExpression (0) [(-7864320, 39), (7864320, 438)],
      Arithmetic.linearExpression (0) [(1, 440)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source8_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (8 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source8 (p := p)) := rfl

def source8Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 423, -7864320 * w 39 + 7864320 * w 438, w 440, 0, 0, 4]

theorem source8_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source8.map (Expression.eval (Verification.environment w)) = source8Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source8, source8Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source9 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 421)],
      Arithmetic.linearExpression (0) [(-7864320, 40), (7864320, 439)],
      Arithmetic.linearExpression (0) [(1, 441)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source9_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (9 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source9 (p := p)) := rfl

def source9Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 421, -7864320 * w 40 + 7864320 * w 439, w 441, 0, 0, 4]

theorem source9_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source9.map (Expression.eval (Verification.environment w)) = source9Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source9, source9Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source10 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 422)],
      Arithmetic.linearExpression (0) [(1, 438)],
      Arithmetic.linearExpression (0) [(30720, 39), (-30720, 155), (-30720, 171), (-30720, 224), (-30720, 226), (-30720, 240), (-30720, 242), (-1, 257), (-3932160, 277), (-30720, 278), (-1, 281), (-30720, 332), (-15728640, 335), (-1, 417), (-3932160, 435), (-30720, 436)],
      Arithmetic.linearExpression (0) [(-7864320, 100), (7864320, 441)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source10_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (10 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source10 (p := p)) := rfl

def source10Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 422, w 438, 30720 * w 39 - 30720 * w 155 - 30720 * w 171 - 30720 * w 224 - 30720 * w 226 - 30720 * w 240 - 30720 * w 242 - w 257 - 3932160 * w 277 - 30720 * w 278 - w 281 - 30720 * w 332 - 15728640 * w 335 - w 417 - 3932160 * w 435 - 30720 * w 436, -7864320 * w 100 + 7864320 * w 441, 0, 55]

theorem source10_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source10.map (Expression.eval (Verification.environment w)) = source10Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source10, source10Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source11 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 420)],
      Arithmetic.linearExpression (0) [(1, 439)],
      Arithmetic.linearExpression (0) [(-943718400, 39), (30720, 40), (943718400, 155), (-30720, 157), (943718400, 171), (-30720, 173), (943718400, 224), (-30720, 225), (943718400, 226), (-30720, 227), (943718400, 240), (-30720, 241), (943718400, 242), (-30720, 243), (-1, 259), (-3932160, 276), (-60, 277), (943718400, 278), (-30720, 279), (-1, 283), (943718400, 332), (-30720, 333), (-15728640, 334), (-240, 335), (-1, 419), (-3932160, 434), (-60, 435), (943718400, 436), (-30720, 437)],
      Arithmetic.linearExpression (0) [(-7864320, 99), (7864320, 440)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source11_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (11 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source11 (p := p)) := rfl

def source11Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 420, w 439, -943718400 * w 39 + 30720 * w 40 + 943718400 * w 155 - 30720 * w 157 + 943718400 * w 171 - 30720 * w 173 + 943718400 * w 224 - 30720 * w 225 + 943718400 * w 226 - 30720 * w 227 + 943718400 * w 240 - 30720 * w 241 + 943718400 * w 242 - 30720 * w 243 - w 259 - 3932160 * w 276 - 60 * w 277 + 943718400 * w 278 - 30720 * w 279 - w 283 + 943718400 * w 332 - 30720 * w 333 - 15728640 * w 334 - 240 * w 335 - w 419 - 3932160 * w 434 - 60 * w 435 + 943718400 * w 436 - 30720 * w 437, -7864320 * w 99 + 7864320 * w 440, 0, 55]

theorem source11_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source11.map (Expression.eval (Verification.environment w)) = source11Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source11, source11Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source12 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 435)],
      Arithmetic.linearExpression (0) [(-15728640, 79), (15728640, 442)],
      Arithmetic.linearExpression (0) [(1, 444)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source12_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (12 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source12 (p := p)) := rfl

def source12Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 435, -15728640 * w 79 + 15728640 * w 442, w 444, 0, 0, 20]

theorem source12_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source12.map (Expression.eval (Verification.environment w)) = source12Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source12, source12Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source13 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 434)],
      Arithmetic.linearExpression (0) [(-15728640, 80), (15728640, 443)],
      Arithmetic.linearExpression (0) [(1, 445)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source13_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (13 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source13 (p := p)) := rfl

def source13Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 434, -15728640 * w 80 + 15728640 * w 443, w 445, 0, 0, 20]

theorem source13_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source13.map (Expression.eval (Verification.environment w)) = source13Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source13, source13Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source14 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 436)],
      Arithmetic.linearExpression (0) [(1, 442)],
      Arithmetic.linearExpression (0) [(30720, 79), (-30720, 99), (-30720, 190), (-30720, 344), (-7864320, 345), (-1, 348), (-30720, 364), (-7864320, 367), (-1, 369), (-30720, 422), (-7864320, 423), (-1, 426)],
      Arithmetic.linearExpression (0) [(-3932160, 60), (3932160, 445)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (56) []]

theorem source14_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (14 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source14 (p := p)) := rfl

def source14Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 436, w 442, 30720 * w 79 - 30720 * w 99 - 30720 * w 190 - 30720 * w 344 - 7864320 * w 345 - w 348 - 30720 * w 364 - 7864320 * w 367 - w 369 - 30720 * w 422 - 7864320 * w 423 - w 426, -3932160 * w 60 + 3932160 * w 445, 0, 56]

theorem source14_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source14.map (Expression.eval (Verification.environment w)) = source14Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source14, source14Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source15 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 437)],
      Arithmetic.linearExpression (0) [(1, 443)],
      Arithmetic.linearExpression (0) [(-943718400, 79), (30720, 80), (943718400, 99), (-30720, 100), (943718400, 190), (-30720, 191), (-30720, 342), (-7864320, 343), (943718400, 344), (-120, 345), (-1, 351), (943718400, 364), (-30720, 365), (-7864320, 366), (-120, 367), (-1, 371), (-30720, 420), (-7864320, 421), (943718400, 422), (-120, 423), (-1, 429)],
      Arithmetic.linearExpression (0) [(-3932160, 59), (3932160, 444)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (56) []]

theorem source15_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (15 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source15 (p := p)) := rfl

def source15Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 437, w 443, -943718400 * w 79 + 30720 * w 80 + 943718400 * w 99 - 30720 * w 100 + 943718400 * w 190 - 30720 * w 191 - 30720 * w 342 - 7864320 * w 343 + 943718400 * w 344 - 120 * w 345 - w 351 + 943718400 * w 364 - 30720 * w 365 - 7864320 * w 366 - 120 * w 367 - w 371 - 30720 * w 420 - 7864320 * w 421 + 943718400 * w 422 - 120 * w 423 - w 429, -3932160 * w 59 + 3932160 * w 444, 0, 56]

theorem source15_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source15.map (Expression.eval (Verification.environment w)) = source15Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source15, source15Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

end Airbender.Blake2Round.Proofs.NativeDiagonalView0
