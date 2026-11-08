module
public import Slop.Blake2Round.GTrace

@[expose] public section

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

open Arithmetic

set_option maxHeartbeats 2000000

/-- Clean's G function, given its eight intermediate words. -/
theorem g_of_steps {a b c d mx my a1 d1 c1 b1 a2 d2 c2 b2 : Nat}
    (ha1 : a1 = add32 a (add32 b mx)) (hd1 : d1 = rotRight32 (d ^^^ a1) 16)
    (hc1 : c1 = add32 c d1) (hb1 : b1 = rotRight32 (b ^^^ c1) 12)
    (ha2 : a2 = add32 a1 (add32 b1 my)) (hd2 : d2 = rotRight32 (d1 ^^^ a2) 8)
    (hc2 : c2 = add32 c1 d2) (hb2 : b2 = rotRight32 (b1 ^^^ c2) 7) :
    let result := Specs.BLAKE3.g #v[a, b, c, d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ mx my
    a2 = result[0] ∧ b2 = result[1] ∧ c2 = result[2] ∧ d2 = result[3] := by
  have native := Blake2G.Proofs.reference_components a b c d mx my
  subst ha1 hd1 hc1 hb1 ha2 hd2 hc2 hb2
  exact ⟨native.1.symm, native.2.1.symm, native.2.2.1.symm, native.2.2.2.symm⟩

theorem byte_pair {x y : Nat} (hx : x < 256) (hy : y < 256) : x + 256 * y < 65536 := by omega

theorem chunk_pair {x y : Nat} (hx : x < 128) (hy : y < 512) : x + 128 * y < 65536 := by omega

theorem chunk_triple {x y z : Nat} (hx : x < 8) (hy : y < 512) (hz : z < 16) :
    x + 8 * y + 4096 * z < 65536 := by omega

/-- The sixteen limb equations over `Nat`, from the chunk bounds. -/
structure GTrace.NatLimbs {p : Nat} (t : GTrace p) : Prop where
  dL : t.dLo.val = t.d0.val + 256 * t.d1.val
  dH : t.dHi.val = t.d2.val + 256 * t.d3.val
  bL : t.bLo.val = t.b3lo.val + 8 * t.b9lo.val + 4096 * t.b4lo.val
  bH : t.bHi.val = t.b3hi.val + 8 * t.b9hi.val + 4096 * t.b4hi.val
  a1L : t.aLo.val + t.bLo.val + t.xLo.val =
    (t.a1b0.val + 256 * t.a1b1.val) + 65536 * t.ka0.val
  a1H : t.aHi.val + t.bHi.val + t.xHi.val + t.ka0.val =
    (t.a1b2.val + 256 * t.a1b3.val) + 65536 * t.ka1.val
  c1L : t.cLo.val + (t.r2.val + 256 * t.r3.val) =
    (t.c3lo.val + 8 * t.c9lo.val + 4096 * t.c4lo.val) + 65536 * t.kc0.val
  c1H : t.cHi.val + (t.r0.val + 256 * t.r1.val) + t.kc0.val =
    (t.c3hi.val + 8 * t.c9hi.val + 4096 * t.c4hi.val) + 65536 * t.kc1.val
  a2L : (t.a1b0.val + 256 * t.a1b1.val) + (t.x7lo.val + 128 * t.x9hi.val) + t.yLo.val =
    (t.a2b0.val + 256 * t.a2b1.val) + 65536 * t.kb0.val
  a2H : (t.a1b2.val + 256 * t.a1b3.val) + (t.x7hi.val + 128 * t.x9lo.val) + t.yHi.val +
    t.kb0.val = (t.a2b2.val + 256 * t.a2b3.val) + 65536 * t.kb1.val
  c2L : (t.c3lo.val + 8 * t.c9lo.val + 4096 * t.c4lo.val) + (t.s0.val + 256 * t.s3.val) =
    (t.c2l0.val + 128 * t.c2h0.val) + 65536 * t.kd0.val
  c2H : (t.c3hi.val + 8 * t.c9hi.val + 4096 * t.c4hi.val) + (t.s1.val + 256 * t.s2.val) +
    t.kd0.val = (t.c2l1.val + 128 * t.c2h1.val) + 65536 * t.kd1.val
  aL : t.a2Lo.val = t.a2b0.val + 256 * t.a2b1.val
  aH : t.a2Hi.val = t.a2b2.val + 256 * t.a2b3.val
  oBL : t.b2Lo.val = t.t0.val + 512 * t.t3.val
  oBH : t.b2Hi.val = t.t1.val + 512 * t.t2.val
  cL : t.c2Lo.val = t.c2l0.val + 128 * t.c2h0.val
  cH : t.c2Hi.val = t.c2l1.val + 128 * t.c2h1.val
  oDL : t.d2Lo.val = t.s0.val + 256 * t.s3.val
  oDH : t.d2Hi.val = t.s1.val + 256 * t.s2.val

/-- Every field equation is an equation of natural numbers below `p`. -/
theorem GTrace.nat_limbs {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p) {t : GTrace p}
    (f : t.Facts) (aB : t.aLo.val < 65536 ∧ t.aHi.val < 65536)
    (xB : t.xLo.val < 65536 ∧ t.xHi.val < 65536) (yB : t.yLo.val < 65536 ∧ t.yHi.val < 65536)
    (cB : t.cLo.val < 65536 ∧ t.cHi.val < 65536) : t.NatLimbs := by
  obtain ⟨aLB, aHB⟩ := aB
  obtain ⟨xLB, xHB⟩ := xB
  obtain ⟨yLB, yHB⟩ := yB
  obtain ⟨cLB, cHB⟩ := cB
  have d0 : t.d0.val < 256 := f.q0.1
  have d1 : t.d1.val < 256 := f.q1.1
  have d2 : t.d2.val < 256 := f.q2.1
  have d3 : t.d3.val < 256 := f.q3.1
  have e0 : t.a1b0.val < 256 := f.q0.2.1
  have e1 : t.a1b1.val < 256 := f.q1.2.1
  have e2 : t.a1b2.val < 256 := f.q2.2.1
  have e3 : t.a1b3.val < 256 := f.q3.2.1
  have r0 : t.r0.val < 256 := f.q0.out
  have r1 : t.r1.val < 256 := f.q1.out
  have r2 : t.r2.val < 256 := f.q2.out
  have r3 : t.r3.val < 256 := f.q3.out
  have b9l : t.b9lo.val < 512 := f.q4.1
  have b9h : t.b9hi.val < 512 := f.q5.1
  have c9l : t.c9lo.val < 512 := f.q4.2.1
  have c9h : t.c9hi.val < 512 := f.q5.2.1
  have x9l : t.x9lo.val < 512 := f.q4.out
  have x9h : t.x9hi.val < 512 := f.q5.out
  have b4l : t.b4lo.val < 16 := f.q6.1
  have b3h : t.b3hi.val < 8 := f.q6.2.1
  have c4l : t.c4lo.val < 16 := f.q6.2.2.1
  have c3h : t.c3hi.val < 8 := f.q6.2.2.2.1
  have b4h : t.b4hi.val < 16 := f.q7.1
  have b3l : t.b3lo.val < 8 := f.q7.2.1
  have c4h : t.c4hi.val < 16 := f.q7.2.2.1
  have c3l : t.c3lo.val < 8 := f.q7.2.2.2.1
  have x7l : t.x7lo.val < 128 := f.q14.1
  have x7h : t.x7hi.val < 128 := f.q15.1
  have g0 : t.a2b0.val < 256 := f.q10.2.1
  have g1 : t.a2b1.val < 256 := f.q8.2.1
  have g2 : t.a2b2.val < 256 := f.q11.2.1
  have g3 : t.a2b3.val < 256 := f.q9.2.1
  have s0 : t.s0.val < 256 := f.q8.out
  have s1 : t.s1.val < 256 := f.q9.out
  have s2 : t.s2.val < 256 := f.q10.out
  have s3 : t.s3.val < 256 := f.q11.out
  have h0 : t.c2l0.val < 128 := f.q14.2.1
  have h1 : t.c2h0.val < 512 := f.q12.2.1
  have h2 : t.c2l1.val < 128 := f.q15.2.1
  have h3 : t.c2h1.val < 512 := f.q13.2.1
  have t0 : t.t0.val < 512 := f.q12.out
  have t1 : t.t1.val < 512 := f.q13.out
  have t2 : t.t2.val < 128 := f.q14.out
  have t3 : t.t3.val < 128 := f.q15.out
  have ka0 := f.ka0; have ka1 := f.ka1; have kb0 := f.kb0; have kb1 := f.kb1
  have kc0 := f.kc0; have kc1 := f.kc1; have kd0 := f.kd0; have kd1 := f.kd1
  have bL : t.bLo.val = t.b3lo.val + 8 * t.b9lo.val + 4096 * t.b4lo.val := by nat_eq f.bLo
  have bH : t.bHi.val = t.b3hi.val + 8 * t.b9hi.val + 4096 * t.b4hi.val := by nat_eq f.bHi
  exact {
    dL := by nat_eq f.dLo
    dH := by nat_eq f.dHi
    bL := bL
    bH := bH
    a1L := by nat_eq f.a1Lo
    a1H := by nat_eq f.a1Hi
    c1L := by nat_eq f.c1Lo
    c1H := by nat_eq f.c1Hi
    a2L := by nat_eq f.a2Lo'
    a2H := by nat_eq f.a2Hi'
    c2L := by nat_eq f.c2Lo'
    c2H := by nat_eq f.c2Hi'
    aL := by nat_eq f.outALo
    aH := by nat_eq f.outAHi
    oBL := by nat_eq f.outBLo
    oBH := by nat_eq f.outBHi
    cL := by nat_eq f.outCLo
    cH := by nat_eq f.outCHi
    oDL := by nat_eq f.outDLo
    oDH := by nat_eq f.outDHi }

/-- The queries and limb equations of one invocation force Clean's G function,
    given 16-bit `a`, `c` and message limbs. `b` and `d` are ranged by the queries. -/
theorem GTrace.sound {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p) {t : GTrace p}
    (f : t.Facts) (aB : t.input.state.a.Bounded) (cB : t.input.state.c.Bounded)
    (xB : t.input.mx.Bounded) (yB : t.input.my.Bounded) :
    Blake2G.spec t.input t.output := by
  simp only [GTrace.input, Word.Bounded, limbBase] at aB cB xB yB
  have n := GTrace.nat_limbs hp f aB xB yB cB
  have firstA := add3_of_limbs (byte_pair f.q0.2.1 f.q1.2.1) (byte_pair f.q2.2.1 f.q3.2.1)
    n.a1L n.a1H
  have firstD := rotate16_of_bytes f.q0.1 f.q1.1 f.q2.1 f.q0.2.1 f.q1.2.1 f.q2.2.1
    f.q0.2.2 f.q1.2.2 f.q2.2.2 f.q3.2.2 f.q0.out f.q1.out
  have firstC := add2_of_limbs
    (chunk_triple f.q7.2.2.2.1 f.q4.2.1 f.q6.2.2.1) (chunk_triple f.q6.2.2.2.1 f.q5.2.1 f.q7.2.2.1)
    n.c1L n.c1H
  have firstB := rotate12_of_chunks f.q7.2.1 f.q4.1 f.q6.1 f.q6.2.1 f.q5.1 f.q7.1
    f.q7.2.2.2.1 f.q4.2.1 f.q6.2.2.1 f.q6.2.2.2.1 f.q5.2.1 f.q7.2.2.1
    f.q4.2.2 f.q5.2.2 f.q6.2.2.2.2 f.q7.2.2.2.2
  have secondA := add3_of_limbs (byte_pair f.q10.2.1 f.q8.2.1) (byte_pair f.q11.2.1 f.q9.2.1)
    n.a2L n.a2H
  have secondD := rotate8_of_bytes f.q2.out f.q3.out f.q0.out f.q10.2.1 f.q8.2.1 f.q11.2.1
    f.q10.2.2 f.q8.2.2 f.q11.2.2 f.q9.2.2 f.q10.out
  have secondC := add2_of_limbs (chunk_pair f.q14.2.1 f.q12.2.1)
    (chunk_pair f.q15.2.1 f.q13.2.1) n.c2L n.c2H
  have secondB := rotate7_of_chunks f.q14.1 f.q12.1 f.q15.1 f.q14.2.1 f.q12.2.1 f.q15.2.1
    f.q14.2.2 f.q12.2.2 f.q15.2.2 f.q13.2.2
  rw [← n.bL, ← n.bH] at firstB
  rw [← n.dL, ← n.dH] at firstD
  simp only [Blake2G.spec, GTrace.input, GTrace.output, Word.value, limbBase]
  rw [n.aL, n.aH, n.oBL, n.oBH, n.cL, n.cH, n.oDL, n.oDH]
  exact g_of_steps firstA firstD.symm firstC firstB.symm secondA secondD.symm secondC
    secondB.symm

end Airbender.Blake2Round.Proofs
