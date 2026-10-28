import Airbender.Proofs.GKRCompiler.ArithmeticInstances
import Airbender.Proofs.GKRProtocol.PooledExecution
import Airbender.Proofs.GKRProtocol.UnifiedExecution
import Airbender.Proofs.GKRProtocol.LogicalExecution
import Airbender.Proofs.GKRProtocol.ProgramExecution

namespace Airbender.Compiler.Review
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

section
open PooledExecution

/-- Canonically framed captured rows and exact logical matching imply pooled
Sail execution, including consumption of the independent external-read stream. -/
theorem pooled_execution {trace : PooledTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    {stream : List (BitVec 32)} (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    NonDeterminism.Pooled.Realizes stream NativeDecoder.pooledProgram trace before cells
      (ROMView.token before) :=
  PooledExecution.native_execution boundary certificates rowBinding states memory inverse ports

/-- Physical native lookup arguments establish authored membership and helper
ranges before the captured rows compose to pooled execution. Exact state/RAM
matching remains an explicit boundary; no canonical borrow frame is imposed. -/
theorem pooled_logical_execution {trace : PooledTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    {stream : List (BitVec 32)} (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    NonDeterminism.Pooled.Realizes stream NativeDecoder.pooledProgram trace before cells
      (ROMView.token before) :=
  PooledExecution.Logical.native_execution boundary certificates rowBinding states memory inverse ports

end

section
open UnifiedExecution

/-- Canonically framed captured rows and exact logical matching imply unified
Sail execution for the retained public program and initial memory. -/
theorem unified_execution {trace : UnifiedTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    (byteInverse : SerializedInverse.Scale256 babyBearModulus) :
    Realizes (UnifiedReduced.Step NativeDecoder.unifiedProgram) trace before cells (ROMView.token before) :=
  UnifiedExecution.native_execution boundary certificates rowBinding states memory inverse byteInverse

/-- Unified captured rows compose from exact physical lookup matching, deriving
the former helper-range and authored-membership certificate fields. -/
theorem unified_logical_execution {trace : UnifiedTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    (byteInverse : SerializedInverse.Scale256 babyBearModulus) :
    Realizes (UnifiedReduced.Step NativeDecoder.unifiedProgram) trace before cells (ROMView.token before) :=
  UnifiedExecution.Logical.native_execution boundary certificates rowBinding states memory inverse byteInverse

end

end Airbender.Compiler.Review
