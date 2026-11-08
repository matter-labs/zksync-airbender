import SailRV32
import Human.Helpers.Core.Word
import Human.Helpers.Core.CircuitOutput

namespace Airbender.Reference.Sail
open _root_.Sail.ArchSem

end Airbender.Reference.Sail

namespace Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
open Airbender.Reference.Sail
open Airbender.Arithmetic

abbrev State := SequentialState SailRV32.RegisterType

export Airbender.Circuit (Output)

end Airbender.Reference.RiscV.Sail
