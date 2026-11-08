import Slop.Sail.PMP
import Human.Helpers.Core.Configuration

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

theorem physical_address_value (address : BitVec 32) :
    (address.setWidth 34).toNat = address.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have bound := address.isLt; omega)

end Airbender.Reference.RiscV.Sail
