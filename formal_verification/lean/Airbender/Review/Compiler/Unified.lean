import Airbender.Review.Helpers.Memory.ImportedImage
import Airbender.Import.Compiler.Rows.UnifiedCached
import Airbender.Import.Compiler.Rows.UnifiedUncached
import Airbender.Review.Helpers.UnifiedReduced.NativeROM

namespace Airbender.Compiler.UnifiedExecution
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail

inductive RowCertificate where
  | plain (cert : UnifiedRowNative.UnifiedUncached.Certificate)
  | preprocessed (cert : UnifiedRowNative.UnifiedCached.Certificate)

def RowCertificate.row : RowCertificate → Row babyBearModulus UnifiedFamily
  | .plain cert => UnifiedRowNative.UnifiedUncached.row cert
  | .preprocessed cert => UnifiedRowNative.UnifiedCached.row cert

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Independent public execution inputs. Compiler constraints and decoded
instructions are proved from the actual framed native rows below. -/
structure PublicBoundary (trace : UnifiedTrace babyBearModulus)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  image : ROM.ImportedImage before
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  profile : InitialProfile before cells
  physicalImage : ∃ tokens : List (MemoryToken babyBearModulus), initialImage before cells = some tokens
  seed : trace.initialMemory = ROMView.nativeBootImage cells
  initialPC : trace.initial = PCState.boundary 0 (4, 0)
  setup : trace.rom = UnifiedReduced.Setup.table before
  registers : ∀ index, Cell.register index ∈ cells
  configuration : FlatMemoryConfiguration before
  ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address
  landingPadDisabled : ∃ security, before.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0

end Airbender.Compiler.UnifiedExecution
