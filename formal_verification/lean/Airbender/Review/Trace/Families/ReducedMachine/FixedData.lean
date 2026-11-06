import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.Tables.Native
import Airbender.Proofs.Mersenne31

namespace Airbender.ReducedMachine.Native
open Trace

/-- Construct the actual checked fixed-pool trace. Only setup is selected;
    all supplied rows, public state/memory boundaries and matching tokens remain
    explicit. This constructs acceptance at a concrete reference, not a premise
    equating an arbitrary modeled table with the native pool. -/
def fixedData (trace : Data mersenne31Modulus NativeReducedFamily) :
    Data mersenne31Modulus NativeReducedFamily := { trace with rom := NativeFixed.table }

end Airbender.ReducedMachine.Native
