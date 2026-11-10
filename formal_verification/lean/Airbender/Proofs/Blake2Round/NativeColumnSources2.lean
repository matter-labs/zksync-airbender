import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2Round.NativeLayout
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.Ring

namespace Airbender.Blake2Round.Proofs.NativeColumnView2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def source0 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 340)],
      Arithmetic.linearExpression (0) [(1, 336)],
      Arithmetic.linearExpression (0) [(1, 337)],
      Arithmetic.linearExpression (0) [(1, 342)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source0_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (0 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source0 (p := p)) := rfl

def source0Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 340, w 336, w 337, w 342, 0, 55]

theorem source0_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source0.map (Expression.eval (Verification.environment w)) = source0Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source0, source0Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source1 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-7864320, 200), (7864320, 340)],
      Arithmetic.linearExpression (0) [(-7864320, 163), (-7864320, 179), (-7864320, 232), (7864320, 336), (-256, 337)],
      Arithmetic.linearExpression (0) [(1, 343)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source1_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (1 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source1 (p := p)) := rfl

def source1Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-7864320 * w 200 + 7864320 * w 340, -7864320 * w 163 - 7864320 * w 179 - 7864320 * w 232 + 7864320 * w 336 - 256 * w 337, w 343, 0, 0, 4]

theorem source1_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source1.map (Expression.eval (Verification.environment w)) = source1Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source1, source1Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source2 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 341)],
      Arithmetic.linearExpression (0) [(1, 338)],
      Arithmetic.linearExpression (0) [(1, 339)],
      Arithmetic.linearExpression (0) [(1, 344)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source2_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (2 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source2 (p := p)) := rfl

def source2Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 341, w 338, w 339, w 344, 0, 55]

theorem source2_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source2.map (Expression.eval (Verification.environment w)) = source2Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source2, source2Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source3 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-7864320, 201), (7864320, 341)],
      Arithmetic.linearExpression (0) [(-7864320, 165), (-7864320, 181), (-7864320, 233), (-7864320, 337), (7864320, 338), (-256, 339)],
      Arithmetic.linearExpression (0) [(1, 345)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source3_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (3 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source3 (p := p)) := rfl

def source3Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-7864320 * w 201 + 7864320 * w 341, -7864320 * w 165 - 7864320 * w 181 - 7864320 * w 233 - 7864320 * w 337 + 7864320 * w 338 - 256 * w 339, w 345, 0, 0, 4]

theorem source3_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source3.map (Expression.eval (Verification.environment w)) = source3Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source3, source3Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source4 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 353)],
      Arithmetic.linearExpression (0) [(1, 347)],
      Arithmetic.linearExpression (0) [(1, 356)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source4_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (4 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source4 (p := p)) := rfl

def source4Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 353, w 347, w 356, 0, 0, 20]

theorem source4_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source4.map (Expression.eval (Verification.environment w)) = source4Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source4, source4Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source5 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 355)],
      Arithmetic.linearExpression (0) [(1, 350)],
      Arithmetic.linearExpression (0) [(1, 357)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source5_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (5 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source5 (p := p)) := rfl

def source5Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 355, w 350, w 357, 0, 0, 20]

theorem source5_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source5.map (Expression.eval (Verification.environment w)) = source5Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source5, source5Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source6 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 179), (491520, 352), (3932160, 353)],
      Arithmetic.linearExpression (0) [(1, 354)],
      Arithmetic.linearExpression (0) [(-491520, 190), (-491520, 344), (-125829120, 345), (491520, 346), (3932160, 347), (-16, 348)],
      Arithmetic.linearExpression (0) [(1, 349)],
      Arithmetic.linearExpression (0) [(1, 358)],
      Arithmetic.linearExpression (57) []]

theorem source6_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source6 (p := p)) := rfl

def source6Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 179 + 491520 * w 352 + 3932160 * w 353, w 354, -491520 * w 190 - 491520 * w 344 - 125829120 * w 345 + 491520 * w 346 + 3932160 * w 347 - 16 * w 348, w 349, w 358, 57]

theorem source6_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source6.map (Expression.eval (Verification.environment w)) = source6Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source6, source6Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source7 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 181), (491520, 354), (3932160, 355)],
      Arithmetic.linearExpression (0) [(1, 352)],
      Arithmetic.linearExpression (0) [(-491520, 191), (-491520, 342), (-125829120, 343), (-491520, 348), (491520, 349), (3932160, 350), (-16, 351)],
      Arithmetic.linearExpression (0) [(1, 346)],
      Arithmetic.linearExpression (0) [(1, 359)],
      Arithmetic.linearExpression (57) []]

theorem source7_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (7 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source7 (p := p)) := rfl

def source7Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 181 + 491520 * w 354 + 3932160 * w 355, w 352, -491520 * w 191 - 491520 * w 342 - 125829120 * w 343 - 491520 * w 348 + 491520 * w 349 + 3932160 * w 350 - 16 * w 351, w 346, w 359, 57]

theorem source7_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source7.map (Expression.eval (Verification.environment w)) = source7Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source7, source7Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source8 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 345)],
      Arithmetic.linearExpression (0) [(-7864320, 163), (-7864320, 179), (-7864320, 232), (-7864320, 234), (-256, 337), (-1006632960, 357), (-7864320, 358), (7864320, 360), (-256, 361)],
      Arithmetic.linearExpression (0) [(1, 364)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source8_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (8 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source8 (p := p)) := rfl

def source8Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 345, -7864320 * w 163 - 7864320 * w 179 - 7864320 * w 232 - 7864320 * w 234 - 256 * w 337 - 1006632960 * w 357 - 7864320 * w 358 + 7864320 * w 360 - 256 * w 361, w 364, 0, 0, 4]

theorem source8_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source8.map (Expression.eval (Verification.environment w)) = source8Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source8, source8Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source9 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 343)],
      Arithmetic.linearExpression (0) [(-7864320, 165), (-7864320, 181), (-7864320, 233), (-7864320, 235), (-7864320, 337), (-256, 339), (-1006632960, 356), (-7864320, 359), (-7864320, 361), (7864320, 362), (-256, 363)],
      Arithmetic.linearExpression (0) [(1, 365)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source9_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (9 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source9 (p := p)) := rfl

def source9Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 343, -7864320 * w 165 - 7864320 * w 181 - 7864320 * w 233 - 7864320 * w 235 - 7864320 * w 337 - 256 * w 339 - 1006632960 * w 356 - 7864320 * w 359 - 7864320 * w 361 + 7864320 * w 362 - 256 * w 363, w 365, 0, 0, 4]

theorem source9_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source9.map (Expression.eval (Verification.environment w)) = source9Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source9, source9Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source10 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 344)],
      Arithmetic.linearExpression (0) [(1, 360)],
      Arithmetic.linearExpression (0) [(1, 361)],
      Arithmetic.linearExpression (0) [(1, 366)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source10_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (10 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source10 (p := p)) := rfl

def source10Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 344, w 360, w 361, w 366, 0, 55]

theorem source10_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source10.map (Expression.eval (Verification.environment w)) = source10Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source10, source10Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source11 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 342)],
      Arithmetic.linearExpression (0) [(1, 362)],
      Arithmetic.linearExpression (0) [(1, 363)],
      Arithmetic.linearExpression (0) [(1, 367)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source11_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (11 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source11 (p := p)) := rfl

def source11Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 342, w 362, w 363, w 367, 0, 55]

theorem source11_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source11.map (Expression.eval (Verification.environment w)) = source11Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source11, source11Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source12 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 357)],
      Arithmetic.linearExpression (0) [(-15728640, 190), (-15728640, 344), (2, 345), (-512, 348), (-15728640, 364), (2, 367), (15728640, 368), (-512, 369)],
      Arithmetic.linearExpression (0) [(1, 372)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source12_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (12 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source12 (p := p)) := rfl

def source12Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 357, -15728640 * w 190 - 15728640 * w 344 + 2 * w 345 - 512 * w 348 - 15728640 * w 364 + 2 * w 367 + 15728640 * w 368 - 512 * w 369, w 372, 0, 0, 20]

theorem source12_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source12.map (Expression.eval (Verification.environment w)) = source12Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source12, source12Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source13 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 356)],
      Arithmetic.linearExpression (0) [(-15728640, 191), (-15728640, 342), (2, 343), (-15728640, 348), (-512, 351), (-15728640, 365), (2, 366), (-15728640, 369), (15728640, 370), (-512, 371)],
      Arithmetic.linearExpression (0) [(1, 373)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source13_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (13 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source13 (p := p)) := rfl

def source13Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 356, -15728640 * w 191 - 15728640 * w 342 + 2 * w 343 - 15728640 * w 348 - 512 * w 351 - 15728640 * w 365 + 2 * w 366 - 15728640 * w 369 + 15728640 * w 370 - 512 * w 371, w 373, 0, 0, 20]

theorem source13_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source13.map (Expression.eval (Verification.environment w)) = source13Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source13, source13Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source14 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 358)],
      Arithmetic.linearExpression (0) [(1, 368)],
      Arithmetic.linearExpression (0) [(1, 374)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (19) []]

theorem source14_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (14 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source14 (p := p)) := rfl

def source14Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 358, w 368, w 374, 0, 0, 19]

theorem source14_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source14.map (Expression.eval (Verification.environment w)) = source14Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source14, source14Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source15 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 359)],
      Arithmetic.linearExpression (0) [(1, 370)],
      Arithmetic.linearExpression (0) [(1, 375)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (19) []]

theorem source15_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (15 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source15 (p := p)) := rfl

def source15Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 359, w 370, w 375, 0, 0, 19]

theorem source15_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source15.map (Expression.eval (Verification.environment w)) = source15Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source15, source15Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

end Airbender.Blake2Round.Proofs.NativeColumnView2
