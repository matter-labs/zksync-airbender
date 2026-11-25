module
public import Human.Circuits.UnifiedReduced.Proth120Artifact
public import Human.Circuits.InitsTeardowns.Theorems

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open InitsTeardowns Trace

/-- At every position in either inline set, its public uint8 window number selects the same aligned
    RV32 address for the zero boot token and for the teardown token carrying the native columns. -/
def WindowTokensClaim : Prop :=
  ∀ (w : Witness proth120Modulus importedLayout) (s : Fin importedLayout.sets.size)
    (r : Fin (2 ^ importedLayout.traceLog)), w.topBits[s] < 256 →
    let addr := windowAddress importedLayout w.topBits[s] r
    let set := importedLayout.sets[s]
    addr < 2 ^ 31 ∧ (Cell.ram (BitVec.ofNat 32 addr)).Aligned ∧
      initToken (p := proth120Modulus) importedLayout w.topBits[s] r =
        (Cell.ram (BitVec.ofNat 32 addr)).initialToken 0 ∧
      teardownToken importedLayout set w.topBits[s] r (w.assignment r) =
        ⟨(Cell.ram (BitVec.ofNat 32 addr)).addressCode, rawPair (w.assignment r) set.timestamp,
          pairCode (w.assignment r) set.value⟩

/-- Both the last window and the last row of an actual set are admissible. -/
def WindowTokensSatisfiableClaim : Prop :=
  ∃ (w : Witness proth120Modulus importedLayout) (s : Fin importedLayout.sets.size)
    (r : Fin (2 ^ importedLayout.traceLog)), w.topBits[s] < 256 ∧
      w.topBits[s] = 255 ∧ r.val + 1 = 2 ^ importedLayout.traceLog

end Airbender.UnifiedReduced.Proth120
