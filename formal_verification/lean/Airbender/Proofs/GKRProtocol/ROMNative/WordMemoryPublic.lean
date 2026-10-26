import Airbender.Proofs.GKRProtocol.ROMNative.WordMemory
import Airbender.Proofs.GKRProtocol.CleanClosedNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanClosedNative.WordMemoryCached

namespace Airbender.Compiler.ROMNative.WordMemory
open Airbender Airbender.Compiler
set_option warningAsError true

/-- The exact table used by the complete uncached Clean witness reads public
bytes; no table equality or witness read value is supplied as a premise. -/
theorem uncached_rom_reads {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) :
    Trace.ROM.Reads (p := babyBearModulus) before
      Airbender.Compiler.CleanClosedNative.WordMemoryUncached.nativeSetup :=
  native_rom_reads image

/-- Cached preprocessing uses the same checked materialized public table. -/
theorem cached_rom_reads {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) :
    Trace.ROM.Reads (p := babyBearModulus) before
      Airbender.Compiler.CleanClosedNative.WordMemoryCached.nativeSetup :=
  native_rom_reads image

end Airbender.Compiler.ROMNative.WordMemory
