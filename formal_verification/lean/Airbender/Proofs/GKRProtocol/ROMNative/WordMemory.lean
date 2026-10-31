import Airbender.Proofs.GKRProtocol.ROMNative.WordMemoryRows
import Airbender.Proofs.GKRProtocol.ColumnSlices
import Airbender.Proofs.GKRProtocol.MaterializedNative.WordMemoryUncached
import Airbender.Proofs.Tables.ImportedROMReads

namespace Airbender.Compiler.ROMNative.WordMemory
open Airbender Airbender.Compiler
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem native_rom_reads {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) :
    Trace.ROM.Reads (p := babyBearModulus) before (nativeSetup.imported.data.table "Airbender.Native.WordMemory") := by
  intro address lo hi bounded high member
  apply Trace.ROM.Proofs.imported_reads (p := babyBearModulus) (by decide +kernel) image address lo hi bounded high
  exact active_rom_refinement member rfl

end Airbender.Compiler.ROMNative.WordMemory
