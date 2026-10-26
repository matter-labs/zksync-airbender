import Airbender.Proofs.GKRCompiler.ArithmeticInstances
import Airbender.Proofs.GKRProtocol.PooledExecution
import Airbender.Proofs.GKRProtocol.UnifiedExecution

namespace Airbender.Compiler.Review
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail

/-- Native arithmetic implies every original source assertion and Boolean
obligation for each of the 22 captured configurations. -/
theorem source_preserved (configuration : Configuration)
    {values : Fin (arithmeticCapture configuration).lowerVariables → Source.BaseField}
    (holds : (arithmeticCapture configuration).artifact.LoweredHolds values) :
    (arithmeticCapture configuration).artifact.SourceHolds
      (values ∘ (arithmeticCapture configuration).artifact.placement) :=
  ArithmeticInstances.source_preserved configuration holds

/-- Source arithmetic has an extension satisfying the explicitly selected native
arithmetic slice. Complete graph construction is a separate supporting result. -/
theorem source_extends (configuration : Configuration)
    {values : Fin (arithmeticCapture configuration).sourceVariables → Source.BaseField}
    (holds : (arithmeticCapture configuration).artifact.SourceHolds values) :
    ∃ extended : Fin (arithmeticCapture configuration).lowerVariables → Source.BaseField,
      (∀ wire, extended ((arithmeticCapture configuration).artifact.placement wire) = values wire) ∧
      (∀ index ∈ (arithmeticCapture configuration).selected,
        ((arithmeticCapture configuration).artifact.gates.get index).expressionResidual extended = 0) :=
  ArithmeticInstances.source_extends configuration holds

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

end

end Airbender.Compiler.Review
