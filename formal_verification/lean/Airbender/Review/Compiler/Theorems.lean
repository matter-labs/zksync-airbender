import Airbender.Compatibility.Compiler
import Airbender.Proofs.GKRCompiler.ArithmeticInstances
import Airbender.Proofs.GKRProtocol.PooledExecution
import Airbender.Proofs.GKRProtocol.UnifiedExecution
import Airbender.Proofs.GKRProtocol.LogicalExecution
import Airbender.Proofs.GKRProtocol.ProgramExecution

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

/-- Captured compiler execution for a supplied public program whose decoder
table has the stated structural interpretation. No per-row decoder membership,
helper range, authored membership or execution result is supplied. -/
theorem pooled_program_execution {trace : PooledTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {program : List PooledProgramEntry}
    (boundary : ProgramBoundary trace before cells program) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    {stream : List (BitVec 32)} (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    NonDeterminism.Pooled.Realizes stream program trace before cells (ROMView.token before) :=
  PooledExecution.Logical.program_execution boundary certificates rowBinding states memory inverse ports

end

section
open UnifiedExecution

/-- Unified execution for a supplied public program and a structural decoder
table interpretation of this capture. The fixed retained setup remains part
of the premise; arbitrary new setup captures require interpretation evidence. -/
theorem unified_program_execution {trace : UnifiedTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry}
    (boundary : ProgramBoundary trace before cells program) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    (byteInverse : SerializedInverse.Scale256 babyBearModulus) :
    Realizes (UnifiedReduced.Step program) trace before cells (ROMView.token before) :=
  UnifiedExecution.Logical.program_execution boundary certificates rowBinding states memory inverse byteInverse

end

section AirbenderPlatform

omit [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] in
/-- The pooled compiler entrypoint explicitly selects Airbender's disabled
device windows while preserving the supplied platform's remaining routing. -/
theorem pooled_airbender_execution
    (platform : _root_.Sail.ArchSem.MemoryPlatform SailRV32.exception) :
    letI : _root_.Sail.ArchSem.MemoryPlatform SailRV32.exception := platform.airbender;
    ∀ {trace : PooledTrace babyBearModulus}
      {before : Reference.RiscV.Sail.State} {cells : List Cell} {program : List PooledProgramEntry}
      (boundary : PooledExecution.ProgramBoundary trace before cells program)
      (certificates : List PooledExecution.LogicalRowCertificate)
      (rowBinding : trace.rows = certificates.map PooledExecution.LogicalRowCertificate.row)
      (states : (trace.initial :: trace.rows.map Row.finish).Perm
        (trace.terminal :: trace.rows.map Row.start))
      (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
        (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
      (inverse : SerializedInverse.Clock babyBearModulus)
      {stream : List (BitVec 32)} (ports : NonDeterminism.Pooled.StreamPorts trace stream),
      NonDeterminism.Pooled.Realizes stream program trace before cells (ROMView.token before) := by
  letI : _root_.Sail.ArchSem.MemoryPlatform SailRV32.exception := platform.airbender
  intro trace before cells program boundary certificates rowBinding states memory inverse stream ports
  exact pooled_program_execution boundary certificates rowBinding states memory inverse ports

omit [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] in
/-- The unified compiler entrypoint explicitly selects Airbender's device
configuration; it does not inherit the upstream-device default. -/
theorem unified_airbender_execution
    (platform : _root_.Sail.ArchSem.MemoryPlatform SailRV32.exception) :
    letI : _root_.Sail.ArchSem.MemoryPlatform SailRV32.exception := platform.airbender;
    ∀ {trace : UnifiedTrace babyBearModulus}
      {before : Reference.RiscV.Sail.State} {cells : List Cell}
      {program : List UnifiedReduced.ProgramEntry}
      (boundary : UnifiedExecution.ProgramBoundary trace before cells program)
      (certificates : List UnifiedExecution.LogicalRowCertificate)
      (rowBinding : trace.rows = certificates.map UnifiedExecution.LogicalRowCertificate.row)
      (states : (trace.initial :: trace.rows.map Row.finish).Perm
        (trace.terminal :: trace.rows.map Row.start))
      (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
        (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
      (inverse : SerializedInverse.Clock babyBearModulus)
      (byteInverse : SerializedInverse.Scale256 babyBearModulus),
      Realizes (UnifiedReduced.Step program) trace before cells (ROMView.token before) := by
  letI : _root_.Sail.ArchSem.MemoryPlatform SailRV32.exception := platform.airbender
  intro trace before cells program boundary certificates rowBinding states memory inverse byteInverse
  exact unified_program_execution boundary certificates rowBinding states memory inverse byteInverse

end AirbenderPlatform

end Airbender.Compiler.Review
