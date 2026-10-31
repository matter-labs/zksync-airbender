import Airbender.Review.Helpers.Memory.ImportedImage
import Airbender.Review.Compiler.ROMDomain
import Airbender.Import.Compiler.Rows.AddSubCached
import Airbender.Import.Compiler.Rows.AddSubUncached
import Airbender.Import.Compiler.Rows.JumpBranchCached
import Airbender.Import.Compiler.Rows.JumpBranchUncached
import Airbender.Import.Compiler.Rows.MulDivCached
import Airbender.Import.Compiler.Rows.MulDivUncached
import Airbender.Import.Compiler.Rows.ShiftBinopCached
import Airbender.Import.Compiler.Rows.ShiftBinopUncached
import Airbender.Import.Compiler.Rows.SubwordMemoryCached
import Airbender.Import.Compiler.Rows.SubwordMemoryUncached
import Airbender.Import.Compiler.Rows.WordMemoryCached
import Airbender.Import.Compiler.Rows.WordMemoryUncached
import Airbender.Review.Helpers.Context.PooledBoundary
import Airbender.Review.Helpers.Decoder.PooledProgram

namespace Airbender.Compiler.PooledExecution
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail

/-- Each physical row retains its actual family and cache-mode proof. -/
inductive RowCertificate where
  | addSubUncached (cert : PooledRowNative.AddSubUncached.Certificate)
  | addSubCached (cert : PooledRowNative.AddSubCached.Certificate)
  | jumpBranchUncached (cert : PooledRowNative.JumpBranchUncached.Certificate)
  | jumpBranchCached (cert : PooledRowNative.JumpBranchCached.Certificate)
  | mulDivUncached (cert : PooledRowNative.MulDivUncached.Certificate)
  | mulDivCached (cert : PooledRowNative.MulDivCached.Certificate)
  | shiftBinopUncached (cert : PooledRowNative.ShiftBinopUncached.Certificate)
  | shiftBinopCached (cert : PooledRowNative.ShiftBinopCached.Certificate)
  | wordMemoryUncached (cert : PooledRowNative.WordMemoryUncached.Certificate)
  | wordMemoryCached (cert : PooledRowNative.WordMemoryCached.Certificate)
  | subwordMemoryUncached (cert : PooledRowNative.SubwordMemoryUncached.Certificate)
  | subwordMemoryCached (cert : PooledRowNative.SubwordMemoryCached.Certificate)

def RowCertificate.row : RowCertificate → Row babyBearModulus PooledFamily
  | .addSubUncached cert => PooledRowNative.AddSubUncached.row cert
  | .addSubCached cert => PooledRowNative.AddSubCached.row cert
  | .jumpBranchUncached cert => PooledRowNative.JumpBranchUncached.row cert
  | .jumpBranchCached cert => PooledRowNative.JumpBranchCached.row cert
  | .mulDivUncached cert => PooledRowNative.MulDivUncached.row cert
  | .mulDivCached cert => PooledRowNative.MulDivCached.row cert
  | .shiftBinopUncached cert => PooledRowNative.ShiftBinopUncached.row cert
  | .shiftBinopCached cert => PooledRowNative.ShiftBinopCached.row cert
  | .wordMemoryUncached cert => PooledRowNative.WordMemoryUncached.row cert
  | .wordMemoryCached cert => PooledRowNative.WordMemoryCached.row cert
  | .subwordMemoryUncached cert => PooledRowNative.SubwordMemoryUncached.row cert
  | .subwordMemoryCached cert => PooledRowNative.SubwordMemoryCached.row cert

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public starting state, domain and verifier boundary. No per-row result,
constraint validity or decoder membership is assumed by these fields. -/
structure PublicBoundary (trace : PooledTrace babyBearModulus)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  image : ROM.ImportedImage before
  domain : ROMNative.WordFullPublic.CoversROM cells
  registers : ∀ index, Cell.register index ∈ cells
  ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address
  configuration : FlatMemoryConfiguration before
  landingPadDisabled : ∃ security, before.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  profile : InitialProfile before cells
  seed : trace.initialMemory = ROMView.nativeBootImage cells
  initialBoundary : trace.initial = PCState.boundary 0 (4, 0)
  physicalImage : ∃ tokens, initialImage before cells = some tokens ∧
    trace.rom.wordMemory = ROM.table cells tokens
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words before)
  verifierBoundary : VerifierBoundary.BootClosure trace.initial
    (trace.rows.map Row.start) (trace.rows.map Row.finish)

end Airbender.Compiler.PooledExecution
