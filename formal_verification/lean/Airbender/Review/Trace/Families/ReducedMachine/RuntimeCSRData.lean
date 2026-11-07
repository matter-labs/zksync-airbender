import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimePool
import Airbender.Proofs.Mersenne31

namespace Airbender.ReducedMachine.Native
open Trace

/-- Construct the explicit constructed runtime-CSR pool trace with retained ROM. Only setup is selected;
    all supplied rows, public state/memory boundaries and matching tokens remain
    explicit. This constructs acceptance at a concrete reference, not a premise
    equating an arbitrary modeled table with the native pool. -/
def runtimeCSRData (trace : Data mersenne31Modulus NativeReducedFamily) :
    Data mersenne31Modulus NativeReducedFamily := { trace with rom := NativeRuntimePool.table }

end Airbender.ReducedMachine.Native
