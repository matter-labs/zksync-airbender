import GKRProtocol.ROMNative.Unified
import GKRProtocol.CleanClosedNative.UnifiedUncached
import GKRProtocol.CleanClosedNative.UnifiedCached

namespace Airbender.Compiler.ROMNative.Unified
open Airbender Airbender.Compiler
set_option warningAsError true

theorem uncached_public_rom_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {query : Vector Source.BaseField 10}
    (member : Airbender.Compiler.CleanClosedNative.UnifiedUncached.nativeSetup.Contains #[] query)
    (tag : query[9] = 34) :
    (UnifiedReduced.Setup.table (p := babyBearModulus) before).Contains #[] query :=
  public_rom_refinement image member tag

theorem cached_public_rom_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {query : Vector Source.BaseField 10}
    (member : Airbender.Compiler.CleanClosedNative.UnifiedCached.nativeSetup.Contains #[] query)
    (tag : query[9] = 34) :
    (UnifiedReduced.Setup.table (p := babyBearModulus) before).Contains #[] query :=
  public_rom_refinement image member tag

end Airbender.Compiler.ROMNative.Unified
