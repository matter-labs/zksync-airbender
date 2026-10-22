import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2Round.NativeLayout
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.Ring

namespace Airbender.Blake2Round.Proofs.NativeDiagonalView2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def source0 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 324)],
      Arithmetic.linearExpression (0) [(1, 476)],
      Arithmetic.linearExpression (0) [(1, 477)],
      Arithmetic.linearExpression (0) [(1, 480)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source0_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (0 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source0 (p := p)) := rfl

def source0Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 324, w 476, w 477, w 480, 0, 55]

theorem source0_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source0.map (Expression.eval (Verification.environment w)) = source0Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source0, source0Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source1 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 327)],
      Arithmetic.linearExpression (0) [(-7864320, 163), (-7864320, 179), (-7864320, 232), (-7864320, 234), (-7864320, 248), (-256, 337), (-1006632960, 357), (-7864320, 358), (-256, 361), (-7864320, 412), (2, 415), (7864320, 476), (-256, 477)],
      Arithmetic.linearExpression (0) [(1, 481)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source1_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (1 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source1 (p := p)) := rfl

def source1Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 327, -7864320 * w 163 - 7864320 * w 179 - 7864320 * w 232 - 7864320 * w 234 - 7864320 * w 248 - 256 * w 337 - 1006632960 * w 357 - 7864320 * w 358 - 256 * w 361 - 7864320 * w 412 + 2 * w 415 + 7864320 * w 476 - 256 * w 477, w 481, 0, 0, 4]

theorem source1_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source1.map (Expression.eval (Verification.environment w)) = source1Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source1, source1Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source2 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 325)],
      Arithmetic.linearExpression (0) [(1, 478)],
      Arithmetic.linearExpression (0) [(1, 479)],
      Arithmetic.linearExpression (0) [(1, 482)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source2_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (2 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source2 (p := p)) := rfl

def source2Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 325, w 478, w 479, w 482, 0, 55]

theorem source2_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source2.map (Expression.eval (Verification.environment w)) = source2Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source2, source2Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source3 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 326)],
      Arithmetic.linearExpression (0) [(-7864320, 165), (-7864320, 181), (-7864320, 233), (-7864320, 235), (-7864320, 249), (-7864320, 337), (-256, 339), (-1006632960, 356), (-7864320, 359), (-7864320, 361), (-256, 363), (-7864320, 413), (2, 414), (-7864320, 477), (7864320, 478), (-256, 479)],
      Arithmetic.linearExpression (0) [(1, 483)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source3_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (3 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source3 (p := p)) := rfl

def source3Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 326, -7864320 * w 165 - 7864320 * w 181 - 7864320 * w 233 - 7864320 * w 235 - 7864320 * w 249 - 7864320 * w 337 - 256 * w 339 - 1006632960 * w 356 - 7864320 * w 359 - 7864320 * w 361 - 256 * w 363 - 7864320 * w 413 + 2 * w 414 - 7864320 * w 477 + 7864320 * w 478 - 256 * w 479, w 483, 0, 0, 4]

theorem source3_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source3.map (Expression.eval (Verification.environment w)) = source3Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source3, source3Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source4 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 491)],
      Arithmetic.linearExpression (0) [(1, 485)],
      Arithmetic.linearExpression (0) [(1, 494)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source4_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (4 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source4 (p := p)) := rfl

def source4Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 491, w 485, w 494, 0, 0, 20]

theorem source4_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source4.map (Expression.eval (Verification.environment w)) = source4Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source4, source4Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source5 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 493)],
      Arithmetic.linearExpression (0) [(1, 488)],
      Arithmetic.linearExpression (0) [(1, 495)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source5_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (5 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source5 (p := p)) := rfl

def source5Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 493, w 488, w 495, 0, 0, 20]

theorem source5_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source5.map (Expression.eval (Verification.environment w)) = source5Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source5, source5Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source6 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 412), (-251658240, 415), (491520, 490), (3932160, 491)],
      Arithmetic.linearExpression (0) [(1, 492)],
      Arithmetic.linearExpression (0) [(-491520, 186), (-491520, 264), (-125829120, 265), (-16, 268), (-491520, 284), (-125829120, 287), (-16, 289), (-491520, 482), (-125829120, 483), (491520, 484), (3932160, 485), (-16, 486)],
      Arithmetic.linearExpression (0) [(1, 487)],
      Arithmetic.linearExpression (0) [(1, 496)],
      Arithmetic.linearExpression (57) []]

theorem source6_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source6 (p := p)) := rfl

def source6Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 412 - 251658240 * w 415 + 491520 * w 490 + 3932160 * w 491, w 492, -491520 * w 186 - 491520 * w 264 - 125829120 * w 265 - 16 * w 268 - 491520 * w 284 - 125829120 * w 287 - 16 * w 289 - 491520 * w 482 - 125829120 * w 483 + 491520 * w 484 + 3932160 * w 485 - 16 * w 486, w 487, w 496, 57]

theorem source6_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source6.map (Expression.eval (Verification.environment w)) = source6Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source6, source6Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source7 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 413), (-251658240, 414), (491520, 492), (3932160, 493)],
      Arithmetic.linearExpression (0) [(1, 490)],
      Arithmetic.linearExpression (0) [(-491520, 187), (-491520, 262), (-125829120, 263), (-491520, 268), (-16, 271), (-491520, 285), (-125829120, 286), (-491520, 289), (-16, 291), (-491520, 480), (-125829120, 481), (-491520, 486), (491520, 487), (3932160, 488), (-16, 489)],
      Arithmetic.linearExpression (0) [(1, 484)],
      Arithmetic.linearExpression (0) [(1, 497)],
      Arithmetic.linearExpression (57) []]

theorem source7_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (7 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source7 (p := p)) := rfl

def source7Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 413 - 251658240 * w 414 + 491520 * w 492 + 3932160 * w 493, w 490, -491520 * w 187 - 491520 * w 262 - 125829120 * w 263 - 491520 * w 268 - 16 * w 271 - 491520 * w 285 - 125829120 * w 286 - 491520 * w 289 - 16 * w 291 - 491520 * w 480 - 125829120 * w 481 - 491520 * w 486 + 491520 * w 487 + 3932160 * w 488 - 16 * w 489, w 484, w 497, 57]

theorem source7_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source7.map (Expression.eval (Verification.environment w)) = source7Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source7, source7Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source8 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 483)],
      Arithmetic.linearExpression (0) [(-7864320, 47), (7864320, 498)],
      Arithmetic.linearExpression (0) [(1, 500)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source8_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (8 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source8 (p := p)) := rfl

def source8Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 483, -7864320 * w 47 + 7864320 * w 498, w 500, 0, 0, 4]

theorem source8_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source8.map (Expression.eval (Verification.environment w)) = source8Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source8, source8Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source9 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 481)],
      Arithmetic.linearExpression (0) [(-7864320, 48), (7864320, 499)],
      Arithmetic.linearExpression (0) [(1, 501)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source9_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (9 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source9 (p := p)) := rfl

def source9Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 481, -7864320 * w 48 + 7864320 * w 499, w 501, 0, 0, 4]

theorem source9_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source9.map (Expression.eval (Verification.environment w)) = source9Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source9, source9Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source10 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 482)],
      Arithmetic.linearExpression (0) [(1, 498)],
      Arithmetic.linearExpression (0) [(30720, 47), (-30720, 163), (-30720, 179), (-30720, 232), (-30720, 234), (-30720, 248), (-30720, 250), (-1, 337), (-3932160, 357), (-30720, 358), (-1, 361), (-30720, 412), (-15728640, 415), (-1, 477), (-3932160, 495), (-30720, 496)],
      Arithmetic.linearExpression (0) [(-7864320, 92), (7864320, 501)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source10_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (10 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source10 (p := p)) := rfl

def source10Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 482, w 498, 30720 * w 47 - 30720 * w 163 - 30720 * w 179 - 30720 * w 232 - 30720 * w 234 - 30720 * w 248 - 30720 * w 250 - w 337 - 3932160 * w 357 - 30720 * w 358 - w 361 - 30720 * w 412 - 15728640 * w 415 - w 477 - 3932160 * w 495 - 30720 * w 496, -7864320 * w 92 + 7864320 * w 501, 0, 55]

theorem source10_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source10.map (Expression.eval (Verification.environment w)) = source10Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source10, source10Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source11 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 480)],
      Arithmetic.linearExpression (0) [(1, 499)],
      Arithmetic.linearExpression (0) [(-943718400, 47), (30720, 48), (943718400, 163), (-30720, 165), (943718400, 179), (-30720, 181), (943718400, 232), (-30720, 233), (943718400, 234), (-30720, 235), (943718400, 248), (-30720, 249), (943718400, 250), (-30720, 251), (-1, 339), (-3932160, 356), (-60, 357), (943718400, 358), (-30720, 359), (-1, 363), (943718400, 412), (-30720, 413), (-15728640, 414), (-240, 415), (-1, 479), (-3932160, 494), (-60, 495), (943718400, 496), (-30720, 497)],
      Arithmetic.linearExpression (0) [(-7864320, 91), (7864320, 500)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source11_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (11 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source11 (p := p)) := rfl

def source11Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 480, w 499, -943718400 * w 47 + 30720 * w 48 + 943718400 * w 163 - 30720 * w 165 + 943718400 * w 179 - 30720 * w 181 + 943718400 * w 232 - 30720 * w 233 + 943718400 * w 234 - 30720 * w 235 + 943718400 * w 248 - 30720 * w 249 + 943718400 * w 250 - 30720 * w 251 - w 339 - 3932160 * w 356 - 60 * w 357 + 943718400 * w 358 - 30720 * w 359 - w 363 + 943718400 * w 412 - 30720 * w 413 - 15728640 * w 414 - 240 * w 415 - w 479 - 3932160 * w 494 - 60 * w 495 + 943718400 * w 496 - 30720 * w 497, -7864320 * w 91 + 7864320 * w 500, 0, 55]

theorem source11_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source11.map (Expression.eval (Verification.environment w)) = source11Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source11, source11Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source12 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 495)],
      Arithmetic.linearExpression (0) [(-15728640, 71), (15728640, 502)],
      Arithmetic.linearExpression (0) [(1, 504)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source12_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (12 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source12 (p := p)) := rfl

def source12Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 495, -15728640 * w 71 + 15728640 * w 502, w 504, 0, 0, 20]

theorem source12_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source12.map (Expression.eval (Verification.environment w)) = source12Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source12, source12Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source13 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 494)],
      Arithmetic.linearExpression (0) [(-15728640, 72), (15728640, 503)],
      Arithmetic.linearExpression (0) [(1, 505)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source13_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (13 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source13 (p := p)) := rfl

def source13Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 494, -15728640 * w 72 + 15728640 * w 503, w 505, 0, 0, 20]

theorem source13_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source13.map (Expression.eval (Verification.environment w)) = source13Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source13, source13Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source14 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 496)],
      Arithmetic.linearExpression (0) [(1, 502)],
      Arithmetic.linearExpression (0) [(30720, 71), (-30720, 91), (-30720, 186), (-30720, 264), (-7864320, 265), (-1, 268), (-30720, 284), (-7864320, 287), (-1, 289), (-30720, 482), (-7864320, 483), (-1, 486)],
      Arithmetic.linearExpression (0) [(-3932160, 68), (3932160, 505)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (56) []]

theorem source14_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (14 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source14 (p := p)) := rfl

def source14Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 496, w 502, 30720 * w 71 - 30720 * w 91 - 30720 * w 186 - 30720 * w 264 - 7864320 * w 265 - w 268 - 30720 * w 284 - 7864320 * w 287 - w 289 - 30720 * w 482 - 7864320 * w 483 - w 486, -3932160 * w 68 + 3932160 * w 505, 0, 56]

theorem source14_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source14.map (Expression.eval (Verification.environment w)) = source14Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source14, source14Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source15 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 497)],
      Arithmetic.linearExpression (0) [(1, 503)],
      Arithmetic.linearExpression (0) [(-943718400, 71), (30720, 72), (943718400, 91), (-30720, 92), (943718400, 186), (-30720, 187), (-30720, 262), (-7864320, 263), (943718400, 264), (-120, 265), (-1, 271), (943718400, 284), (-30720, 285), (-7864320, 286), (-120, 287), (-1, 291), (-30720, 480), (-7864320, 481), (943718400, 482), (-120, 483), (-1, 489)],
      Arithmetic.linearExpression (0) [(-3932160, 67), (3932160, 504)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (56) []]

theorem source15_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (15 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source15 (p := p)) := rfl

def source15Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 497, w 503, -943718400 * w 71 + 30720 * w 72 + 943718400 * w 91 - 30720 * w 92 + 943718400 * w 186 - 30720 * w 187 - 30720 * w 262 - 7864320 * w 263 + 943718400 * w 264 - 120 * w 265 - w 271 + 943718400 * w 284 - 30720 * w 285 - 7864320 * w 286 - 120 * w 287 - w 291 - 30720 * w 480 - 7864320 * w 481 + 943718400 * w 482 - 120 * w 483 - w 489, -3932160 * w 67 + 3932160 * w 504, 0, 56]

theorem source15_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source15.map (Expression.eval (Verification.environment w)) = source15Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source15, source15Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

end Airbender.Blake2Round.Proofs.NativeDiagonalView2
