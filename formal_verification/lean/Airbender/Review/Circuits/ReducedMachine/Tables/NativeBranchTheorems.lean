import Airbender.Proofs.ReducedMachine.NativeBranchCleanup

namespace Airbender.ReducedMachine.NativeFixed
set_option autoImplicit false

/-- Every accepted actual tag17 query has canonical key and exact bit1/cleared outputs. -/
theorem cleanup_implementation {key bit cleaned : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,bit,cleaned,17]) :
    key.val < 65536 ∧ bit = (key.val / 2 % 2 : Nat) ∧ cleaned = (4*(key.val / 4) : Nat) :=
  NativeBranchCleanupProofs.values member

end Airbender.ReducedMachine.NativeFixed
