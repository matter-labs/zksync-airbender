import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2Round.NativeLayout
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.Ring

namespace Airbender.Blake2Round.Proofs.NativeColumnView3
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def source0 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 380)],
      Arithmetic.linearExpression (0) [(1, 376)],
      Arithmetic.linearExpression (0) [(1, 377)],
      Arithmetic.linearExpression (0) [(1, 382)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source0_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (0 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source0 (p := p)) := rfl

def source0Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 380, w 376, w 377, w 382, 0, 55]

theorem source0_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source0.map (Expression.eval (Verification.environment w)) = source0Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source0, source0Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source1 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-7864320, 196), (7864320, 380)],
      Arithmetic.linearExpression (0) [(-7864320, 167), (-7864320, 183), (-7864320, 236), (7864320, 376), (-256, 377)],
      Arithmetic.linearExpression (0) [(1, 383)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source1_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (1 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source1 (p := p)) := rfl

def source1Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-7864320 * w 196 + 7864320 * w 380, -7864320 * w 167 - 7864320 * w 183 - 7864320 * w 236 + 7864320 * w 376 - 256 * w 377, w 383, 0, 0, 4]

theorem source1_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source1.map (Expression.eval (Verification.environment w)) = source1Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source1, source1Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source2 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 381)],
      Arithmetic.linearExpression (0) [(1, 378)],
      Arithmetic.linearExpression (0) [(1, 379)],
      Arithmetic.linearExpression (0) [(1, 384)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source2_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (2 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source2 (p := p)) := rfl

def source2Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 381, w 378, w 379, w 384, 0, 55]

theorem source2_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source2.map (Expression.eval (Verification.environment w)) = source2Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source2, source2Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source3 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-7864320, 197), (7864320, 381)],
      Arithmetic.linearExpression (0) [(-7864320, 169), (-7864320, 185), (-7864320, 237), (-7864320, 377), (7864320, 378), (-256, 379)],
      Arithmetic.linearExpression (0) [(1, 385)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source3_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (3 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source3 (p := p)) := rfl

def source3Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-7864320 * w 197 + 7864320 * w 381, -7864320 * w 169 - 7864320 * w 185 - 7864320 * w 237 - 7864320 * w 377 + 7864320 * w 378 - 256 * w 379, w 385, 0, 0, 4]

theorem source3_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source3.map (Expression.eval (Verification.environment w)) = source3Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source3, source3Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source4 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 393)],
      Arithmetic.linearExpression (0) [(1, 387)],
      Arithmetic.linearExpression (0) [(1, 396)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source4_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (4 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source4 (p := p)) := rfl

def source4Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 393, w 387, w 396, 0, 0, 20]

theorem source4_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source4.map (Expression.eval (Verification.environment w)) = source4Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source4, source4Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source5 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 395)],
      Arithmetic.linearExpression (0) [(1, 390)],
      Arithmetic.linearExpression (0) [(1, 397)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source5_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (5 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source5 (p := p)) := rfl

def source5Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 395, w 390, w 397, 0, 0, 20]

theorem source5_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source5.map (Expression.eval (Verification.environment w)) = source5Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source5, source5Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source6 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 183), (491520, 392), (3932160, 393)],
      Arithmetic.linearExpression (0) [(1, 394)],
      Arithmetic.linearExpression (0) [(-491520, 192), (-491520, 384), (-125829120, 385), (491520, 386), (3932160, 387), (-16, 388)],
      Arithmetic.linearExpression (0) [(1, 389)],
      Arithmetic.linearExpression (0) [(1, 398)],
      Arithmetic.linearExpression (57) []]

theorem source6_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source6 (p := p)) := rfl

def source6Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 183 + 491520 * w 392 + 3932160 * w 393, w 394, -491520 * w 192 - 491520 * w 384 - 125829120 * w 385 + 491520 * w 386 + 3932160 * w 387 - 16 * w 388, w 389, w 398, 57]

theorem source6_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source6.map (Expression.eval (Verification.environment w)) = source6Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source6, source6Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source7 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 185), (491520, 394), (3932160, 395)],
      Arithmetic.linearExpression (0) [(1, 392)],
      Arithmetic.linearExpression (0) [(-491520, 193), (-491520, 382), (-125829120, 383), (-491520, 388), (491520, 389), (3932160, 390), (-16, 391)],
      Arithmetic.linearExpression (0) [(1, 386)],
      Arithmetic.linearExpression (0) [(1, 399)],
      Arithmetic.linearExpression (57) []]

theorem source7_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (7 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source7 (p := p)) := rfl

def source7Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 185 + 491520 * w 394 + 3932160 * w 395, w 392, -491520 * w 193 - 491520 * w 382 - 125829120 * w 383 - 491520 * w 388 + 491520 * w 389 + 3932160 * w 390 - 16 * w 391, w 386, w 399, 57]

theorem source7_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source7.map (Expression.eval (Verification.environment w)) = source7Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source7, source7Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source8 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 385)],
      Arithmetic.linearExpression (0) [(-7864320, 167), (-7864320, 183), (-7864320, 236), (-7864320, 238), (-256, 377), (-1006632960, 397), (-7864320, 398), (7864320, 400), (-256, 401)],
      Arithmetic.linearExpression (0) [(1, 404)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source8_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (8 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source8 (p := p)) := rfl

def source8Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 385, -7864320 * w 167 - 7864320 * w 183 - 7864320 * w 236 - 7864320 * w 238 - 256 * w 377 - 1006632960 * w 397 - 7864320 * w 398 + 7864320 * w 400 - 256 * w 401, w 404, 0, 0, 4]

theorem source8_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source8.map (Expression.eval (Verification.environment w)) = source8Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source8, source8Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source9 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 383)],
      Arithmetic.linearExpression (0) [(-7864320, 169), (-7864320, 185), (-7864320, 237), (-7864320, 239), (-7864320, 377), (-256, 379), (-1006632960, 396), (-7864320, 399), (-7864320, 401), (7864320, 402), (-256, 403)],
      Arithmetic.linearExpression (0) [(1, 405)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source9_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (9 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source9 (p := p)) := rfl

def source9Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 383, -7864320 * w 169 - 7864320 * w 185 - 7864320 * w 237 - 7864320 * w 239 - 7864320 * w 377 - 256 * w 379 - 1006632960 * w 396 - 7864320 * w 399 - 7864320 * w 401 + 7864320 * w 402 - 256 * w 403, w 405, 0, 0, 4]

theorem source9_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source9.map (Expression.eval (Verification.environment w)) = source9Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source9, source9Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source10 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 384)],
      Arithmetic.linearExpression (0) [(1, 400)],
      Arithmetic.linearExpression (0) [(1, 401)],
      Arithmetic.linearExpression (0) [(1, 406)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source10_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (10 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source10 (p := p)) := rfl

def source10Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 384, w 400, w 401, w 406, 0, 55]

theorem source10_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source10.map (Expression.eval (Verification.environment w)) = source10Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source10, source10Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source11 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 382)],
      Arithmetic.linearExpression (0) [(1, 402)],
      Arithmetic.linearExpression (0) [(1, 403)],
      Arithmetic.linearExpression (0) [(1, 407)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source11_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (11 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source11 (p := p)) := rfl

def source11Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 382, w 402, w 403, w 407, 0, 55]

theorem source11_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source11.map (Expression.eval (Verification.environment w)) = source11Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source11, source11Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source12 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 397)],
      Arithmetic.linearExpression (0) [(-15728640, 192), (-15728640, 384), (2, 385), (-512, 388), (-15728640, 404), (2, 407), (15728640, 408), (-512, 409)],
      Arithmetic.linearExpression (0) [(1, 412)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source12_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (12 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source12 (p := p)) := rfl

def source12Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 397, -15728640 * w 192 - 15728640 * w 384 + 2 * w 385 - 512 * w 388 - 15728640 * w 404 + 2 * w 407 + 15728640 * w 408 - 512 * w 409, w 412, 0, 0, 20]

theorem source12_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source12.map (Expression.eval (Verification.environment w)) = source12Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source12, source12Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source13 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 396)],
      Arithmetic.linearExpression (0) [(-15728640, 193), (-15728640, 382), (2, 383), (-15728640, 388), (-512, 391), (-15728640, 405), (2, 406), (-15728640, 409), (15728640, 410), (-512, 411)],
      Arithmetic.linearExpression (0) [(1, 413)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source13_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (13 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source13 (p := p)) := rfl

def source13Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 396, -15728640 * w 193 - 15728640 * w 382 + 2 * w 383 - 15728640 * w 388 - 512 * w 391 - 15728640 * w 405 + 2 * w 406 - 15728640 * w 409 + 15728640 * w 410 - 512 * w 411, w 413, 0, 0, 20]

theorem source13_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source13.map (Expression.eval (Verification.environment w)) = source13Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source13, source13Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source14 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 398)],
      Arithmetic.linearExpression (0) [(1, 408)],
      Arithmetic.linearExpression (0) [(1, 414)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (19) []]

theorem source14_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (14 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source14 (p := p)) := rfl

def source14Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 398, w 408, w 414, 0, 0, 19]

theorem source14_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source14.map (Expression.eval (Verification.environment w)) = source14Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source14, source14Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source15 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 399)],
      Arithmetic.linearExpression (0) [(1, 410)],
      Arithmetic.linearExpression (0) [(1, 415)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (19) []]

theorem source15_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (15 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source15 (p := p)) := rfl

def source15Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 399, w 410, w 415, 0, 0, 19]

theorem source15_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source15.map (Expression.eval (Verification.environment w)) = source15Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source15, source15Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

end Airbender.Blake2Round.Proofs.NativeColumnView3
