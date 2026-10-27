import Airbender.Review.Compiler.Program
import Airbender.Proofs.GKRProtocol.PooledExecution
import Airbender.Proofs.GKRProtocol.UnifiedExecution

namespace Airbender.Compiler
open Airbender Airbender.Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

namespace PooledExecution

def ProgramBoundary.ofRetained {trace : PooledTrace babyBearModulus}
    {before : State} {cells : List Cell} (boundary : PublicBoundary trace before cells) :
    ProgramBoundary trace before cells NativeDecoder.pooledProgram :=
  ⟨boot_inputs boundary, boundary.image, boundary.domain, fun _ => rfl⟩

def ProgramBoundary.publicBoundary {trace : PooledTrace babyBearModulus}
    {before : State} {cells : List Cell} {program : List PooledProgramEntry}
    (boundary : ProgramBoundary trace before cells program) : PublicBoundary trace before cells := {
  image := boundary.image
  domain := boundary.domain
  registers := boundary.execution.registers
  ordinary := boundary.execution.ordinary
  configuration := boundary.execution.configuration
  landingPadDisabled := boundary.execution.landingPadDisabled
  distinct := boundary.execution.distinct
  aligned := boundary.execution.aligned
  profile := boundary.execution.profile
  seed := boundary.execution.seed
  initialBoundary := boundary.execution.initialBoundary
  physicalImage := boundary.execution.physicalImage
  subwordSetup := boundary.execution.subwordSetup
  verifierBoundary := boundary.execution.verifierBoundary }

theorem program_execution {trace : PooledTrace babyBearModulus}
    {before : State} {cells : List Cell} {program : List PooledProgramEntry}
    (boundary : ProgramBoundary trace before cells program) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    {stream : List (BitVec 32)} (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    NonDeterminism.Pooled.Realizes stream program trace before cells (ROMView.token before) := by
  have native := accepted boundary.publicBoundary certificates rowBinding states memory
  have initial : trace.initial.word.lo < Arithmetic.limbBase := by
    rw [boundary.execution.initialBoundary]
    decide +kernel
  have retained := decoded certificates rowBinding native initial
  have interpreted : PooledDecoded trace program := by
    intro row member
    rw [← boundary.decoderTables row.family]
    exact retained row member
  exact NonDeterminism.Pooled.Proofs.native_trace_execution (by decide +kernel) inverse
    boundary.execution native interpreted ports

end PooledExecution

namespace UnifiedExecution

def ProgramBoundary.ofRetained {trace : UnifiedTrace babyBearModulus}
    {before : State} {cells : List Cell} (boundary : PublicBoundary trace before cells) :
    ProgramBoundary trace before cells NativeDecoder.unifiedProgram :=
  ⟨boot_inputs boundary, boundary.image, fun _ => rfl⟩

/-- Only the setup/table/boot fields required by compiler acceptance are
projected from the existing execution input contract. -/
theorem program_accepted_and_decoded {trace : UnifiedTrace babyBearModulus}
    {before : State} {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (boundary : ProgramBoundary trace before cells program) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads)) :
    Accepted trace ∧ UnifiedReduced.Decoded trace program := by
  have native := native_accepted certificates rowBinding states memory
  have initial : (nativeView trace).initial.word.lo < Arithmetic.limbBase := by
    change trace.initial.word.lo < Arithmetic.limbBase
    rw [boundary.execution.boot.initialPC]
    decide +kernel
  have ranges := NativeDecoder.Proofs.unified_query_pc_low native initial
  have constraints : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom) := by
    intro row member
    have typed := ranges row member
    rw [rowBinding] at member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
    rw [boundary.execution.boot.setup]
    exact row_constraints cert boundary.image typed
  refine ⟨⟨constraints, native.active, states, memory⟩, ?_⟩
  intro row member
  have typed := ranges row member
  rw [rowBinding] at member
  obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
  have retained := row_decoded cert typed
  rw [boundary.decoderTables cert.row.family] at retained
  cases cert <;> exact retained

theorem program_execution {trace : UnifiedTrace babyBearModulus}
    {before : State} {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (boundary : ProgramBoundary trace before cells program) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    (byteInverse : SerializedInverse.Scale256 babyBearModulus) :
    Realizes (UnifiedReduced.Step program) trace before cells (ROMView.token before) := by
  obtain ⟨native, interpreted⟩ := program_accepted_and_decoded boundary certificates rowBinding states memory
  exact UnifiedReduced.Proofs.trace_execution (by decide +kernel) inverse byteInverse
    boundary.execution native interpreted

end UnifiedExecution
end Airbender.Compiler
