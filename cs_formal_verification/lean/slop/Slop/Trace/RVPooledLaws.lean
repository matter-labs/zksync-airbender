module
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Memory.History
public import Slop.Trace.ZeroValues
public import Slop.Trace.History

@[expose] public section

/-! Contract (lean-strategies §2.2) of the whole-trace laws of the pooled RV route whose proofs need every
    family's row lemmas: the pooled clock laws, x0 preservation and
    value bounds. The per-family RV proofs take
    `RVPooledLaws` as a hypothesis and import only this module; `Slop.Trace.RVPooledLawsProof` proves it once, and the
    final theorems (`Slop/Final/Circuits/*/RVTheorems.lean`) combine the two. So an edit to one family's row lemma
    rebuilds the law proof and the final theorems, not the other families' proofs. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- The pooled RV route's whole-trace laws (statements of `rv_pooled_zero_preserving` and
    `rv_pooled_value_bounds`). -/
structure RVPooledLaws : Prop where
  /-- The pooled clock laws (the `ClockLaws PooledFamily` instance, built from every family's clock proofs). -/
  clockLaws : ∀ {p : Nat} [Fact p.Prime], ClockLaws PooledFamily p
  /-- Every row of an accepted RV-decoded pooled trace preserves x0. -/
  zeroPreserving : ∀ {p : Nat} [Fact p.Prime], 196608 < p →
    ∀ {trace : PooledTrace p}, Accepted trace →
    ∀ {initial : RV.State} {addresses : List (BitVec 32)} {program : List RVPooledProgramEntry},
      rvProgramImageWith rvPooledDecoderFields initial addresses = some program →
      RVPooledDecoded trace program → ZeroPreserving trace
  /-- Read, write and terminal values are bounded words. -/
  valueBounds : ∀ {p : Nat} [Fact p.Prime], 33554432 < p → (-3840 : ZMod p) * 524288 = 1 →
    ∀ {trace : PooledTrace p}, Accepted trace → ClockBoundary trace →
    ∀ {initial : RV.State} {cells : List Cell},
      initialImageRV initial cells = some trace.initialMemory →
      trace.rom.wordMemory = ROM.table cells (romImageRV initial cells) →
    ∀ {values : Nat → BitVec 32}, trace.rom.subwordMemory = Verification.subwordTable values →
    ∀ {addresses : List (BitVec 32)} {program : List RVPooledProgramEntry},
      rvProgramImageWith rvPooledDecoderFields initial addresses = some program →
      RVPooledDecoded trace program →
      (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ trace.terminalMemory, token.word.Bounded)

end Airbender.Trace.Proofs
