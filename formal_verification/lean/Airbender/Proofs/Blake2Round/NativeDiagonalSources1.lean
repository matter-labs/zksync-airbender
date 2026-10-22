import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2Round.NativeLayout
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.Ring

namespace Airbender.Blake2Round.Proofs.NativeDiagonalView1
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def source0 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 284)],
      Arithmetic.linearExpression (0) [(1, 446)],
      Arithmetic.linearExpression (0) [(1, 447)],
      Arithmetic.linearExpression (0) [(1, 450)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source0_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (0 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source0 (p := p)) := rfl

def source0Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 284, w 446, w 447, w 450, 0, 55]

theorem source0_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source0.map (Expression.eval (Verification.environment w)) = source0Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source0, source0Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source1 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 287)],
      Arithmetic.linearExpression (0) [(-7864320, 159), (-7864320, 175), (-7864320, 228), (-7864320, 230), (-7864320, 244), (-256, 297), (-1006632960, 317), (-7864320, 318), (-256, 321), (-7864320, 372), (2, 375), (7864320, 446), (-256, 447)],
      Arithmetic.linearExpression (0) [(1, 451)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source1_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (1 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source1 (p := p)) := rfl

def source1Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 287, -7864320 * w 159 - 7864320 * w 175 - 7864320 * w 228 - 7864320 * w 230 - 7864320 * w 244 - 256 * w 297 - 1006632960 * w 317 - 7864320 * w 318 - 256 * w 321 - 7864320 * w 372 + 2 * w 375 + 7864320 * w 446 - 256 * w 447, w 451, 0, 0, 4]

theorem source1_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source1.map (Expression.eval (Verification.environment w)) = source1Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source1, source1Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source2 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 285)],
      Arithmetic.linearExpression (0) [(1, 448)],
      Arithmetic.linearExpression (0) [(1, 449)],
      Arithmetic.linearExpression (0) [(1, 452)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source2_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (2 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source2 (p := p)) := rfl

def source2Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 285, w 448, w 449, w 452, 0, 55]

theorem source2_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source2.map (Expression.eval (Verification.environment w)) = source2Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source2, source2Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source3 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 286)],
      Arithmetic.linearExpression (0) [(-7864320, 161), (-7864320, 177), (-7864320, 229), (-7864320, 231), (-7864320, 245), (-7864320, 297), (-256, 299), (-1006632960, 316), (-7864320, 319), (-7864320, 321), (-256, 323), (-7864320, 373), (2, 374), (-7864320, 447), (7864320, 448), (-256, 449)],
      Arithmetic.linearExpression (0) [(1, 453)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source3_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (3 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source3 (p := p)) := rfl

def source3Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 286, -7864320 * w 161 - 7864320 * w 177 - 7864320 * w 229 - 7864320 * w 231 - 7864320 * w 245 - 7864320 * w 297 - 256 * w 299 - 1006632960 * w 316 - 7864320 * w 319 - 7864320 * w 321 - 256 * w 323 - 7864320 * w 373 + 2 * w 374 - 7864320 * w 447 + 7864320 * w 448 - 256 * w 449, w 453, 0, 0, 4]

theorem source3_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source3.map (Expression.eval (Verification.environment w)) = source3Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source3, source3Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source4 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 461)],
      Arithmetic.linearExpression (0) [(1, 455)],
      Arithmetic.linearExpression (0) [(1, 464)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source4_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (4 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source4 (p := p)) := rfl

def source4Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 461, w 455, w 464, 0, 0, 20]

theorem source4_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source4.map (Expression.eval (Verification.environment w)) = source4Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source4, source4Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source5 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 463)],
      Arithmetic.linearExpression (0) [(1, 458)],
      Arithmetic.linearExpression (0) [(1, 465)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source5_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (5 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source5 (p := p)) := rfl

def source5Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 463, w 458, w 465, 0, 0, 20]

theorem source5_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source5.map (Expression.eval (Verification.environment w)) = source5Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source5, source5Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source6 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 372), (-251658240, 375), (491520, 460), (3932160, 461)],
      Arithmetic.linearExpression (0) [(1, 462)],
      Arithmetic.linearExpression (0) [(-491520, 192), (-491520, 384), (-125829120, 385), (-16, 388), (-491520, 404), (-125829120, 407), (-16, 409), (-491520, 452), (-125829120, 453), (491520, 454), (3932160, 455), (-16, 456)],
      Arithmetic.linearExpression (0) [(1, 457)],
      Arithmetic.linearExpression (0) [(1, 466)],
      Arithmetic.linearExpression (57) []]

theorem source6_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source6 (p := p)) := rfl

def source6Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 372 - 251658240 * w 375 + 491520 * w 460 + 3932160 * w 461, w 462, -491520 * w 192 - 491520 * w 384 - 125829120 * w 385 - 16 * w 388 - 491520 * w 404 - 125829120 * w 407 - 16 * w 409 - 491520 * w 452 - 125829120 * w 453 + 491520 * w 454 + 3932160 * w 455 - 16 * w 456, w 457, w 466, 57]

theorem source6_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source6.map (Expression.eval (Verification.environment w)) = source6Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source6, source6Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source7 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 373), (-251658240, 374), (491520, 462), (3932160, 463)],
      Arithmetic.linearExpression (0) [(1, 460)],
      Arithmetic.linearExpression (0) [(-491520, 193), (-491520, 382), (-125829120, 383), (-491520, 388), (-16, 391), (-491520, 405), (-125829120, 406), (-491520, 409), (-16, 411), (-491520, 450), (-125829120, 451), (-491520, 456), (491520, 457), (3932160, 458), (-16, 459)],
      Arithmetic.linearExpression (0) [(1, 454)],
      Arithmetic.linearExpression (0) [(1, 467)],
      Arithmetic.linearExpression (57) []]

theorem source7_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (7 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source7 (p := p)) := rfl

def source7Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 373 - 251658240 * w 374 + 491520 * w 462 + 3932160 * w 463, w 460, -491520 * w 193 - 491520 * w 382 - 125829120 * w 383 - 491520 * w 388 - 16 * w 391 - 491520 * w 405 - 125829120 * w 406 - 491520 * w 409 - 16 * w 411 - 491520 * w 450 - 125829120 * w 451 - 491520 * w 456 + 491520 * w 457 + 3932160 * w 458 - 16 * w 459, w 454, w 467, 57]

theorem source7_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source7.map (Expression.eval (Verification.environment w)) = source7Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source7, source7Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source8 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 453)],
      Arithmetic.linearExpression (0) [(-7864320, 43), (7864320, 468)],
      Arithmetic.linearExpression (0) [(1, 470)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source8_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (8 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source8 (p := p)) := rfl

def source8Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 453, -7864320 * w 43 + 7864320 * w 468, w 470, 0, 0, 4]

theorem source8_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source8.map (Expression.eval (Verification.environment w)) = source8Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source8, source8Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source9 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 451)],
      Arithmetic.linearExpression (0) [(-7864320, 44), (7864320, 469)],
      Arithmetic.linearExpression (0) [(1, 471)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source9_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (9 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source9 (p := p)) := rfl

def source9Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 451, -7864320 * w 44 + 7864320 * w 469, w 471, 0, 0, 4]

theorem source9_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source9.map (Expression.eval (Verification.environment w)) = source9Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source9, source9Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source10 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 452)],
      Arithmetic.linearExpression (0) [(1, 468)],
      Arithmetic.linearExpression (0) [(30720, 43), (-30720, 159), (-30720, 175), (-30720, 228), (-30720, 230), (-30720, 244), (-30720, 246), (-1, 297), (-3932160, 317), (-30720, 318), (-1, 321), (-30720, 372), (-15728640, 375), (-1, 447), (-3932160, 465), (-30720, 466)],
      Arithmetic.linearExpression (0) [(-7864320, 88), (7864320, 471)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source10_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (10 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source10 (p := p)) := rfl

def source10Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 452, w 468, 30720 * w 43 - 30720 * w 159 - 30720 * w 175 - 30720 * w 228 - 30720 * w 230 - 30720 * w 244 - 30720 * w 246 - w 297 - 3932160 * w 317 - 30720 * w 318 - w 321 - 30720 * w 372 - 15728640 * w 375 - w 447 - 3932160 * w 465 - 30720 * w 466, -7864320 * w 88 + 7864320 * w 471, 0, 55]

theorem source10_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source10.map (Expression.eval (Verification.environment w)) = source10Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source10, source10Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source11 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 450)],
      Arithmetic.linearExpression (0) [(1, 469)],
      Arithmetic.linearExpression (0) [(-943718400, 43), (30720, 44), (943718400, 159), (-30720, 161), (943718400, 175), (-30720, 177), (943718400, 228), (-30720, 229), (943718400, 230), (-30720, 231), (943718400, 244), (-30720, 245), (943718400, 246), (-30720, 247), (-1, 299), (-3932160, 316), (-60, 317), (943718400, 318), (-30720, 319), (-1, 323), (943718400, 372), (-30720, 373), (-15728640, 374), (-240, 375), (-1, 449), (-3932160, 464), (-60, 465), (943718400, 466), (-30720, 467)],
      Arithmetic.linearExpression (0) [(-7864320, 87), (7864320, 470)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source11_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (11 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source11 (p := p)) := rfl

def source11Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 450, w 469, -943718400 * w 43 + 30720 * w 44 + 943718400 * w 159 - 30720 * w 161 + 943718400 * w 175 - 30720 * w 177 + 943718400 * w 228 - 30720 * w 229 + 943718400 * w 230 - 30720 * w 231 + 943718400 * w 244 - 30720 * w 245 + 943718400 * w 246 - 30720 * w 247 - w 299 - 3932160 * w 316 - 60 * w 317 + 943718400 * w 318 - 30720 * w 319 - w 323 + 943718400 * w 372 - 30720 * w 373 - 15728640 * w 374 - 240 * w 375 - w 449 - 3932160 * w 464 - 60 * w 465 + 943718400 * w 466 - 30720 * w 467, -7864320 * w 87 + 7864320 * w 470, 0, 55]

theorem source11_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source11.map (Expression.eval (Verification.environment w)) = source11Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source11, source11Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source12 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 465)],
      Arithmetic.linearExpression (0) [(-15728640, 83), (15728640, 472)],
      Arithmetic.linearExpression (0) [(1, 474)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source12_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (12 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source12 (p := p)) := rfl

def source12Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 465, -15728640 * w 83 + 15728640 * w 472, w 474, 0, 0, 20]

theorem source12_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source12.map (Expression.eval (Verification.environment w)) = source12Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source12, source12Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source13 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 464)],
      Arithmetic.linearExpression (0) [(-15728640, 84), (15728640, 473)],
      Arithmetic.linearExpression (0) [(1, 475)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source13_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (13 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source13 (p := p)) := rfl

def source13Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 464, -15728640 * w 84 + 15728640 * w 473, w 475, 0, 0, 20]

theorem source13_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source13.map (Expression.eval (Verification.environment w)) = source13Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source13, source13Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source14 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 466)],
      Arithmetic.linearExpression (0) [(1, 472)],
      Arithmetic.linearExpression (0) [(30720, 83), (-30720, 87), (-30720, 192), (-30720, 384), (-7864320, 385), (-1, 388), (-30720, 404), (-7864320, 407), (-1, 409), (-30720, 452), (-7864320, 453), (-1, 456)],
      Arithmetic.linearExpression (0) [(-3932160, 64), (3932160, 475)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (56) []]

theorem source14_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (14 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source14 (p := p)) := rfl

def source14Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 466, w 472, 30720 * w 83 - 30720 * w 87 - 30720 * w 192 - 30720 * w 384 - 7864320 * w 385 - w 388 - 30720 * w 404 - 7864320 * w 407 - w 409 - 30720 * w 452 - 7864320 * w 453 - w 456, -3932160 * w 64 + 3932160 * w 475, 0, 56]

theorem source14_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source14.map (Expression.eval (Verification.environment w)) = source14Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source14, source14Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source15 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 467)],
      Arithmetic.linearExpression (0) [(1, 473)],
      Arithmetic.linearExpression (0) [(-943718400, 83), (30720, 84), (943718400, 87), (-30720, 88), (943718400, 192), (-30720, 193), (-30720, 382), (-7864320, 383), (943718400, 384), (-120, 385), (-1, 391), (943718400, 404), (-30720, 405), (-7864320, 406), (-120, 407), (-1, 411), (-30720, 450), (-7864320, 451), (943718400, 452), (-120, 453), (-1, 459)],
      Arithmetic.linearExpression (0) [(-3932160, 63), (3932160, 474)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (56) []]

theorem source15_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (15 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source15 (p := p)) := rfl

def source15Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 467, w 473, -943718400 * w 83 + 30720 * w 84 + 943718400 * w 87 - 30720 * w 88 + 943718400 * w 192 - 30720 * w 193 - 30720 * w 382 - 7864320 * w 383 + 943718400 * w 384 - 120 * w 385 - w 391 + 943718400 * w 404 - 30720 * w 405 - 7864320 * w 406 - 120 * w 407 - w 411 - 30720 * w 450 - 7864320 * w 451 + 943718400 * w 452 - 120 * w 453 - w 459, -3932160 * w 63 + 3932160 * w 474, 0, 56]

theorem source15_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source15.map (Expression.eval (Verification.environment w)) = source15Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source15, source15Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

end Airbender.Blake2Round.Proofs.NativeDiagonalView1
