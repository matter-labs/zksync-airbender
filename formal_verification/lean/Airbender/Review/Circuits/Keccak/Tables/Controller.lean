import Airbender.Review.Circuits.Keccak.Controller

namespace Airbender.Keccak.Controller
set_option warningAsError true

/-- Six lane/scratch outputs from the actual native controller region. Invalid
    and inactive controls retain the exported rows; scheduling stays separate. -/
def rows (key : Fin 4096) : Vector Nat 6 :=
  Vector.ofFn fun j => ((controllerData.columns[j.val + 1]).get? key.val).getD 0

end Airbender.Keccak.Controller
