import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2Round.NativeLayout
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.Ring

namespace Airbender.Blake2Round.Proofs.NativeDiagonalView3
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def source0 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 364)],
      Arithmetic.linearExpression (0) [(1, 506)],
      Arithmetic.linearExpression (0) [(1, 507)],
      Arithmetic.linearExpression (0) [(1, 510)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source0_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (0 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source0 (p := p)) := rfl

def source0Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 364, w 506, w 507, w 510, 0, 55]

theorem source0_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source0.map (Expression.eval (Verification.environment w)) = source0Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source0, source0Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source1 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 367)],
      Arithmetic.linearExpression (0) [(-7864320, 167), (-7864320, 183), (-7864320, 236), (-7864320, 238), (-7864320, 252), (-7864320, 292), (2, 295), (-256, 377), (-1006632960, 397), (-7864320, 398), (-256, 401), (7864320, 506), (-256, 507)],
      Arithmetic.linearExpression (0) [(1, 511)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source1_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (1 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source1 (p := p)) := rfl

def source1Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 367, -7864320 * w 167 - 7864320 * w 183 - 7864320 * w 236 - 7864320 * w 238 - 7864320 * w 252 - 7864320 * w 292 + 2 * w 295 - 256 * w 377 - 1006632960 * w 397 - 7864320 * w 398 - 256 * w 401 + 7864320 * w 506 - 256 * w 507, w 511, 0, 0, 4]

theorem source1_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source1.map (Expression.eval (Verification.environment w)) = source1Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source1, source1Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source2 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 365)],
      Arithmetic.linearExpression (0) [(1, 508)],
      Arithmetic.linearExpression (0) [(1, 509)],
      Arithmetic.linearExpression (0) [(1, 512)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source2_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (2 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source2 (p := p)) := rfl

def source2Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 365, w 508, w 509, w 512, 0, 55]

theorem source2_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source2.map (Expression.eval (Verification.environment w)) = source2Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source2, source2Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source3 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 366)],
      Arithmetic.linearExpression (0) [(-7864320, 169), (-7864320, 185), (-7864320, 237), (-7864320, 239), (-7864320, 253), (-7864320, 293), (2, 294), (-7864320, 377), (-256, 379), (-1006632960, 396), (-7864320, 399), (-7864320, 401), (-256, 403), (-7864320, 507), (7864320, 508), (-256, 509)],
      Arithmetic.linearExpression (0) [(1, 513)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source3_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (3 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source3 (p := p)) := rfl

def source3Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 366, -7864320 * w 169 - 7864320 * w 185 - 7864320 * w 237 - 7864320 * w 239 - 7864320 * w 253 - 7864320 * w 293 + 2 * w 294 - 7864320 * w 377 - 256 * w 379 - 1006632960 * w 396 - 7864320 * w 399 - 7864320 * w 401 - 256 * w 403 - 7864320 * w 507 + 7864320 * w 508 - 256 * w 509, w 513, 0, 0, 4]

theorem source3_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source3.map (Expression.eval (Verification.environment w)) = source3Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source3, source3Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source4 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 521)],
      Arithmetic.linearExpression (0) [(1, 515)],
      Arithmetic.linearExpression (0) [(1, 524)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source4_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (4 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source4 (p := p)) := rfl

def source4Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 521, w 515, w 524, 0, 0, 20]

theorem source4_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source4.map (Expression.eval (Verification.environment w)) = source4Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source4, source4Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source5 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 523)],
      Arithmetic.linearExpression (0) [(1, 518)],
      Arithmetic.linearExpression (0) [(1, 525)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source5_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (5 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source5 (p := p)) := rfl

def source5Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 523, w 518, w 525, 0, 0, 20]

theorem source5_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source5.map (Expression.eval (Verification.environment w)) = source5Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source5, source5Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source6 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 292), (-251658240, 295), (491520, 520), (3932160, 521)],
      Arithmetic.linearExpression (0) [(1, 522)],
      Arithmetic.linearExpression (0) [(-491520, 188), (-491520, 304), (-125829120, 305), (-16, 308), (-491520, 324), (-125829120, 327), (-16, 329), (-491520, 512), (-125829120, 513), (491520, 514), (3932160, 515), (-16, 516)],
      Arithmetic.linearExpression (0) [(1, 517)],
      Arithmetic.linearExpression (0) [(1, 526)],
      Arithmetic.linearExpression (57) []]

theorem source6_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source6 (p := p)) := rfl

def source6Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 292 - 251658240 * w 295 + 491520 * w 520 + 3932160 * w 521, w 522, -491520 * w 188 - 491520 * w 304 - 125829120 * w 305 - 16 * w 308 - 491520 * w 324 - 125829120 * w 327 - 16 * w 329 - 491520 * w 512 - 125829120 * w 513 + 491520 * w 514 + 3932160 * w 515 - 16 * w 516, w 517, w 526, 57]

theorem source6_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source6.map (Expression.eval (Verification.environment w)) = source6Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source6, source6Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source7 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(-491520, 293), (-251658240, 294), (491520, 522), (3932160, 523)],
      Arithmetic.linearExpression (0) [(1, 520)],
      Arithmetic.linearExpression (0) [(-491520, 189), (-491520, 302), (-125829120, 303), (-491520, 308), (-16, 311), (-491520, 325), (-125829120, 326), (-491520, 329), (-16, 331), (-491520, 510), (-125829120, 511), (-491520, 516), (491520, 517), (3932160, 518), (-16, 519)],
      Arithmetic.linearExpression (0) [(1, 514)],
      Arithmetic.linearExpression (0) [(1, 527)],
      Arithmetic.linearExpression (57) []]

theorem source7_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (7 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source7 (p := p)) := rfl

def source7Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[-491520 * w 293 - 251658240 * w 294 + 491520 * w 522 + 3932160 * w 523, w 520, -491520 * w 189 - 491520 * w 302 - 125829120 * w 303 - 491520 * w 308 - 16 * w 311 - 491520 * w 325 - 125829120 * w 326 - 491520 * w 329 - 16 * w 331 - 491520 * w 510 - 125829120 * w 511 - 491520 * w 516 + 491520 * w 517 + 3932160 * w 518 - 16 * w 519, w 514, w 527, 57]

theorem source7_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source7.map (Expression.eval (Verification.environment w)) = source7Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source7, source7Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source8 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 513)],
      Arithmetic.linearExpression (0) [(-7864320, 51), (7864320, 528)],
      Arithmetic.linearExpression (0) [(1, 530)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source8_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (8 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source8 (p := p)) := rfl

def source8Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 513, -7864320 * w 51 + 7864320 * w 528, w 530, 0, 0, 4]

theorem source8_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source8.map (Expression.eval (Verification.environment w)) = source8Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source8, source8Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source9 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 511)],
      Arithmetic.linearExpression (0) [(-7864320, 52), (7864320, 529)],
      Arithmetic.linearExpression (0) [(1, 531)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem source9_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (9 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source9 (p := p)) := rfl

def source9Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 511, -7864320 * w 52 + 7864320 * w 529, w 531, 0, 0, 4]

theorem source9_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source9.map (Expression.eval (Verification.environment w)) = source9Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source9, source9Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source10 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 512)],
      Arithmetic.linearExpression (0) [(1, 528)],
      Arithmetic.linearExpression (0) [(30720, 51), (-30720, 167), (-30720, 183), (-30720, 236), (-30720, 238), (-30720, 252), (-30720, 254), (-30720, 292), (-15728640, 295), (-1, 377), (-3932160, 397), (-30720, 398), (-1, 401), (-1, 507), (-3932160, 525), (-30720, 526)],
      Arithmetic.linearExpression (0) [(-7864320, 96), (7864320, 531)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source10_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (10 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source10 (p := p)) := rfl

def source10Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 512, w 528, 30720 * w 51 - 30720 * w 167 - 30720 * w 183 - 30720 * w 236 - 30720 * w 238 - 30720 * w 252 - 30720 * w 254 - 30720 * w 292 - 15728640 * w 295 - w 377 - 3932160 * w 397 - 30720 * w 398 - w 401 - w 507 - 3932160 * w 525 - 30720 * w 526, -7864320 * w 96 + 7864320 * w 531, 0, 55]

theorem source10_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source10.map (Expression.eval (Verification.environment w)) = source10Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source10, source10Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source11 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 510)],
      Arithmetic.linearExpression (0) [(1, 529)],
      Arithmetic.linearExpression (0) [(-943718400, 51), (30720, 52), (943718400, 167), (-30720, 169), (943718400, 183), (-30720, 185), (943718400, 236), (-30720, 237), (943718400, 238), (-30720, 239), (943718400, 252), (-30720, 253), (943718400, 254), (-30720, 255), (943718400, 292), (-30720, 293), (-15728640, 294), (-240, 295), (-1, 379), (-3932160, 396), (-60, 397), (943718400, 398), (-30720, 399), (-1, 403), (-1, 509), (-3932160, 524), (-60, 525), (943718400, 526), (-30720, 527)],
      Arithmetic.linearExpression (0) [(-7864320, 95), (7864320, 530)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (55) []]

theorem source11_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (11 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source11 (p := p)) := rfl

def source11Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 510, w 529, -943718400 * w 51 + 30720 * w 52 + 943718400 * w 167 - 30720 * w 169 + 943718400 * w 183 - 30720 * w 185 + 943718400 * w 236 - 30720 * w 237 + 943718400 * w 238 - 30720 * w 239 + 943718400 * w 252 - 30720 * w 253 + 943718400 * w 254 - 30720 * w 255 + 943718400 * w 292 - 30720 * w 293 - 15728640 * w 294 - 240 * w 295 - w 379 - 3932160 * w 396 - 60 * w 397 + 943718400 * w 398 - 30720 * w 399 - w 403 - w 509 - 3932160 * w 524 - 60 * w 525 + 943718400 * w 526 - 30720 * w 527, -7864320 * w 95 + 7864320 * w 530, 0, 55]

theorem source11_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source11.map (Expression.eval (Verification.environment w)) = source11Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source11, source11Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source12 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 525)],
      Arithmetic.linearExpression (0) [(-15728640, 75), (15728640, 532)],
      Arithmetic.linearExpression (0) [(1, 534)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source12_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (12 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source12 (p := p)) := rfl

def source12Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 525, -15728640 * w 75 + 15728640 * w 532, w 534, 0, 0, 20]

theorem source12_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source12.map (Expression.eval (Verification.environment w)) = source12Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source12, source12Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source13 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 524)],
      Arithmetic.linearExpression (0) [(-15728640, 76), (15728640, 533)],
      Arithmetic.linearExpression (0) [(1, 535)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem source13_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (13 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source13 (p := p)) := rfl

def source13Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 524, -15728640 * w 76 + 15728640 * w 533, w 535, 0, 0, 20]

theorem source13_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source13.map (Expression.eval (Verification.environment w)) = source13Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source13, source13Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment]

def source14 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 526)],
      Arithmetic.linearExpression (0) [(1, 532)],
      Arithmetic.linearExpression (0) [(30720, 75), (-30720, 95), (-30720, 188), (-30720, 304), (-7864320, 305), (-1, 308), (-30720, 324), (-7864320, 327), (-1, 329), (-30720, 512), (-7864320, 513), (-1, 516)],
      Arithmetic.linearExpression (0) [(-3932160, 56), (3932160, 535)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (56) []]

theorem source14_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (14 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source14 (p := p)) := rfl

def source14Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 526, w 532, 30720 * w 75 - 30720 * w 95 - 30720 * w 188 - 30720 * w 304 - 7864320 * w 305 - w 308 - 30720 * w 324 - 7864320 * w 327 - w 329 - 30720 * w 512 - 7864320 * w 513 - w 516, -3932160 * w 56 + 3932160 * w 535, 0, 56]

theorem source14_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source14.map (Expression.eval (Verification.environment w)) = source14Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source14, source14Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

def source15 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  #v[Arithmetic.linearExpression (0) [(1, 527)],
      Arithmetic.linearExpression (0) [(1, 533)],
      Arithmetic.linearExpression (0) [(-943718400, 75), (30720, 76), (943718400, 95), (-30720, 96), (943718400, 188), (-30720, 189), (-30720, 302), (-7864320, 303), (943718400, 304), (-120, 305), (-1, 311), (943718400, 324), (-30720, 325), (-7864320, 326), (-120, 327), (-1, 331), (-30720, 510), (-7864320, 511), (943718400, 512), (-120, 513), (-1, 519)],
      Arithmetic.linearExpression (0) [(-3932160, 55), (3932160, 534)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (56) []]

theorem source15_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) (15 : Fin 16),
        by rw [lookup_count]; decide⟩) =
      Lookup.mk setupTable.toRaw (source15 (p := p)) := rfl

def source15Values {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 527, w 533, -943718400 * w 75 + 30720 * w 76 + 943718400 * w 95 - 30720 * w 96 + 943718400 * w 188 - 30720 * w 189 - 30720 * w 302 - 7864320 * w 303 + 943718400 * w 304 - 120 * w 305 - w 311 + 943718400 * w 324 - 30720 * w 325 - 7864320 * w 326 - 120 * w 327 - w 331 - 30720 * w 510 - 7864320 * w 511 + 943718400 * w 512 - 120 * w 513 - w 519, -3932160 * w 55 + 3932160 * w 534, 0, 56]

theorem source15_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source15.map (Expression.eval (Verification.environment w)) = source15Values w := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals (simp [source15, source15Values, Arithmetic.linearExpression,
    Expression.eval, Verification.environment] <;> ring)

end Airbender.Blake2Round.Proofs.NativeDiagonalView3
