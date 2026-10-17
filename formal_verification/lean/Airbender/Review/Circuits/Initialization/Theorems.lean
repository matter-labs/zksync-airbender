import Airbender.Proofs.Initialization.Native
import Airbender.Proofs.Initialization.NativeGeometry

namespace Airbender.Initialization
variable {p : Nat} [Fact p.Prime] [CommRing E]

/-- The standalone artifact computes the products of its actual raw RAM
    teardown and zero-initialization tokens. No canonical value/time assumption
    is made. Parsing/Rust refinement and cryptographic logical matching remain
    separate boundaries; sampled product equality is not a permutation proof. -/
theorem standalone_soundness (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (accepted : Accepted standalone parameters raw wires) :
    rootProduct standalone standalone.terminal wires =
        ((ramTokens standalone.layout parameters raw .terminal).map parameters.encode).prod ∧
      rootProduct standalone standalone.initial wires =
        ((ramTokens standalone.layout parameters raw .initial).map parameters.encode).prod :=
  Proofs.standalone_products parameters raw wires accepted

/-- The inline unified artifact uses its own exported RAM output mapping and
    scalar columns. Every native row and both selected sets participate. -/
theorem unified_soundness (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (accepted : Accepted unified parameters raw wires) :
    rootProduct unified unified.terminal wires =
        ((ramTokens unified.layout parameters raw .terminal).map parameters.encode).prod ∧
      rootProduct unified unified.initial wires =
        ((ramTokens unified.layout parameters raw .initial).map parameters.encode).prod :=
  Proofs.unified_products parameters raw wires accepted

end Airbender.Initialization
