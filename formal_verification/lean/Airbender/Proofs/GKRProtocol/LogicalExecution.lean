import Airbender.Review.Compiler.Pooled
import Airbender.Proofs.GKRProtocol.PooledRowNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.PooledRowNative.AddSubCached
import Airbender.Proofs.GKRProtocol.PooledRowNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.PooledRowNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.PooledRowNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.PooledRowNative.MulDivCached
import Airbender.Proofs.GKRProtocol.PooledRowNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.PooledRowNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.PooledRowNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.PooledRowNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.PooledRowNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.PooledRowNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.PublicProgram
import Airbender.Proofs.Tables.DecoderPCLow
import Airbender.Proofs.Trace.PooledOracleComposition
import Airbender.Review.Compiler.LogicalRows
import Airbender.Proofs.GKRProtocol.LogicalRows
import Airbender.Review.Compiler.Unified
import Airbender.Proofs.GKRProtocol.UnifiedRowNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.UnifiedRowNative.UnifiedCached
import Airbender.Proofs.UnifiedReduced.Composition
import Airbender.Proofs.GKRProtocol.ProgramExecution

namespace Airbender.Compiler.PooledExecution.Logical
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem row_active (cert : LogicalRowCertificate) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
  | addSubUncached input _ => exact PooledRowNative.AddSubUncached.input_active input
  | addSubCached input _ => exact PooledRowNative.AddSubCached.input_active input
  | jumpBranchUncached input _ => exact PooledRowNative.JumpBranchUncached.input_active input
  | jumpBranchCached input _ => exact PooledRowNative.JumpBranchCached.input_active input
  | mulDivUncached input _ => exact PooledRowNative.MulDivUncached.input_active input
  | mulDivCached input _ => exact PooledRowNative.MulDivCached.input_active input
  | shiftBinopUncached input _ => exact PooledRowNative.ShiftBinopUncached.input_active input
  | shiftBinopCached input _ => exact PooledRowNative.ShiftBinopCached.input_active input
  | wordMemoryUncached input _ => exact PooledRowNative.WordMemoryUncached.input_active input
  | wordMemoryCached input _ => exact PooledRowNative.WordMemoryCached.input_active input
  | subwordMemoryUncached input _ => exact PooledRowNative.SubwordMemoryUncached.input_active input
  | subwordMemoryCached input _ => exact PooledRowNative.SubwordMemoryCached.input_active input

theorem row_constraints (cert : LogicalRowCertificate) {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) {cells : List Cell}
    {tokens : List (MemoryToken babyBearModulus)}
    (physical : initialImage before cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints (⟨ROM.table cells tokens,
        Verification.subwordTable (ROM.words before)⟩ : PooledSetup babyBearModulus)) := by
  cases cert with
  | addSubUncached input arguments => exact PooledRowNative.AddSubUncached.input_constraints input arguments image physical domain
  | addSubCached input arguments => exact PooledRowNative.AddSubCached.input_constraints input arguments image physical domain
  | jumpBranchUncached input arguments => exact PooledRowNative.JumpBranchUncached.input_constraints input arguments image physical domain
  | jumpBranchCached input arguments => exact PooledRowNative.JumpBranchCached.input_constraints input arguments image physical domain
  | mulDivUncached input arguments => exact PooledRowNative.MulDivUncached.input_constraints input arguments image physical domain
  | mulDivCached input arguments => exact PooledRowNative.MulDivCached.input_constraints input arguments image physical domain
  | shiftBinopUncached input arguments => exact PooledRowNative.ShiftBinopUncached.input_constraints input arguments image physical domain
  | shiftBinopCached input arguments => exact PooledRowNative.ShiftBinopCached.input_constraints input arguments image physical domain
  | wordMemoryUncached input arguments => exact PooledRowNative.WordMemoryUncached.input_constraints input arguments image physical domain
  | wordMemoryCached input arguments => exact PooledRowNative.WordMemoryCached.input_constraints input arguments image physical domain
  | subwordMemoryUncached input arguments => exact PooledRowNative.SubwordMemoryUncached.input_constraints input arguments image physical domain
  | subwordMemoryCached input arguments => exact PooledRowNative.SubwordMemoryCached.input_constraints input arguments image physical domain

theorem row_decoded (cert : LogicalRowCertificate)
    (typed : cert.row.decoderQuery[0].val < 65536) :
    (decoderTable NativeDecoder.pooledProgram cert.row.family).Contains #[]
      cert.row.decoderQuery := by
  cases cert with
  | addSubUncached input arguments => exact PooledRowNative.AddSubUncached.input_decoded input arguments typed
  | addSubCached input arguments => exact PooledRowNative.AddSubCached.input_decoded input arguments typed
  | jumpBranchUncached input arguments => exact PooledRowNative.JumpBranchUncached.input_decoded input arguments typed
  | jumpBranchCached input arguments => exact PooledRowNative.JumpBranchCached.input_decoded input arguments typed
  | mulDivUncached input arguments => exact PooledRowNative.MulDivUncached.input_decoded input arguments typed
  | mulDivCached input arguments => exact PooledRowNative.MulDivCached.input_decoded input arguments typed
  | shiftBinopUncached input arguments => exact PooledRowNative.ShiftBinopUncached.input_decoded input arguments typed
  | shiftBinopCached input arguments => exact PooledRowNative.ShiftBinopCached.input_decoded input arguments typed
  | wordMemoryUncached input arguments => exact PooledRowNative.WordMemoryUncached.input_decoded input arguments typed
  | wordMemoryCached input arguments => exact PooledRowNative.WordMemoryCached.input_decoded input arguments typed
  | subwordMemoryUncached input arguments => exact PooledRowNative.SubwordMemoryUncached.input_decoded input arguments typed
  | subwordMemoryCached input arguments => exact PooledRowNative.SubwordMemoryCached.input_decoded input arguments typed

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

theorem boot_inputs {trace : PooledTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) :
    PooledBootInputs trace before cells NativeDecoder.pooledProgram NonDeterminism.Pooled.decoderFields := by
  exact {
    registers := boundary.registers
    ordinary := boundary.ordinary
    configuration := boundary.configuration
    landingPadDisabled := boundary.landingPadDisabled
    code := PublicProgram.pooled_code
    loads := PublicProgram.pooled_loads
    distinct := boundary.distinct
    aligned := boundary.aligned
    programImage := ⟨_, PublicProgram.pooled_external_image boundary.image⟩
    profile := boundary.profile
    seed := boundary.seed
    initialBoundary := boundary.initialBoundary
    physicalImage := boundary.physicalImage
    subwordSetup := boundary.subwordSetup
    verifierBoundary := boundary.verifierBoundary }

/-- Native arithmetic and exact physical lookup matching construct acceptance.
Exact state and RAM matching remain logical argument-boundary premises. -/
theorem accepted {trace : PooledTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads)) : Accepted trace := by
  obtain ⟨tokens, image, wordSetup⟩ := boundary.physicalImage
  have setup : trace.rom = (⟨ROM.table cells tokens,
      Verification.subwordTable (ROM.words before)⟩ : PooledSetup babyBearModulus) := by
    cases actual : trace.rom with
    | mk word subword =>
      have left := wordSetup
      have right := boundary.subwordSetup
      rw [actual] at left right
      cases left
      cases right
      rfl
  refine ⟨?_, ?_, states, memory⟩
  · intro row member
    rw [rowBinding] at member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
    rw [setup]
    exact row_constraints cert boundary.image image boundary.domain
  · intro row member
    rw [rowBinding] at member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
    exact row_active cert

omit [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] in
theorem decoded {trace : PooledTrace babyBearModulus}
    (certificates : List LogicalRowCertificate) (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
    (native : Accepted trace) (initial : trace.initial.word.lo < Arithmetic.limbBase) :
    PooledDecoded trace NativeDecoder.pooledProgram := by
  have typed := NativeDecoder.Proofs.pooled_query_pc_low (by decide +kernel) native initial
  intro row member
  have range := typed row member
  rw [rowBinding] at member
  obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
  exact row_decoded cert range

/-- Compiler-to-Sail composition for the retained pooled compiler captures.
Constraints and decoding are conclusions. Public configuration, logical matching,
serialized inverses and commitment authentication remain separate boundaries. -/
theorem native_execution {trace : PooledTrace babyBearModulus}
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
      (ROMView.token before) := by
  have native := accepted boundary certificates rowBinding states memory
  have initial : trace.initial.word.lo < Arithmetic.limbBase := by
    rw [boundary.initialBoundary]
    decide +kernel
  exact NonDeterminism.Pooled.Proofs.native_trace_execution (by decide +kernel) inverse
    (boot_inputs boundary) native (decoded certificates rowBinding native initial) ports

end Airbender.Compiler.PooledExecution.Logical


namespace Airbender.Compiler.PooledExecution.Logical
open Airbender Airbender.Trace Reference.RiscV.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
theorem program_execution {trace : PooledTrace babyBearModulus}
    {before : State} {cells : List Cell} {program : List PooledProgramEntry}
    (boundary : ProgramBoundary trace before cells program) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
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

end Airbender.Compiler.PooledExecution.Logical


namespace Airbender.Compiler.UnifiedExecution.Logical
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable abbrev nativeSetup := CleanClosedNative.UnifiedUncached.nativeSetup

noncomputable def nativeView (trace : UnifiedTrace babyBearModulus) : UnifiedTrace babyBearModulus :=
  { trace with rom := nativeSetup }

theorem row_active (cert : LogicalRowCertificate) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
  | plain input _ => exact UnifiedRowNative.UnifiedUncached.input_active input
  | preprocessed input _ => exact UnifiedRowNative.UnifiedCached.input_active input

theorem row_native_constraints (cert : LogicalRowCertificate) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints nativeSetup) := by
  cases cert with
  | plain input arguments => exact UnifiedRowNative.UnifiedUncached.input_native_constraints input arguments
  | preprocessed input arguments => exact UnifiedRowNative.UnifiedCached.input_native_constraints input arguments

theorem row_constraints (cert : LogicalRowCertificate) {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) (typed : cert.row.decoderQuery[0].val < 65536) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints (UnifiedReduced.Setup.table before)) := by
  cases cert with
  | plain input arguments => exact UnifiedRowNative.UnifiedUncached.input_constraints input arguments image typed
  | preprocessed input arguments => exact UnifiedRowNative.UnifiedCached.input_constraints input arguments image typed

theorem row_decoded (cert : LogicalRowCertificate) (typed : cert.row.decoderQuery[0].val < 65536) :
    (decoderTable NativeDecoder.unifiedProgram cert.row.family).Contains #[] cert.row.decoderQuery := by
  cases cert with
  | plain input arguments => exact UnifiedRowNative.UnifiedUncached.input_decoded input arguments typed
  | preprocessed input arguments => exact UnifiedRowNative.UnifiedCached.input_decoded input arguments typed

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

theorem boot_inputs {trace : UnifiedTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) :
    UnifiedReduced.ExecutionInputs trace before cells NativeDecoder.unifiedProgram := by
  exact {
    boot := {
      distinct := boundary.distinct
      aligned := boundary.aligned
      profile := boundary.profile
      image := boundary.physicalImage
      seed := boundary.seed
      initialPC := boundary.initialPC
      programImage := ⟨_, PublicProgram.unified_image boundary.image⟩
      setup := boundary.setup }
    registers := boundary.registers
    code := PublicProgram.unified_code
    configuration := boundary.configuration
    ordinary := boundary.ordinary
    landingPadDisabled := fun _ => boundary.landingPadDisabled
    loads := PublicProgram.unified_loads }

omit [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] in
/-- Acceptance with the actual native table first supplies incoming PC ranges;
public retabling therefore does not assume its own decoder precondition. -/
theorem native_accepted {trace : UnifiedTrace babyBearModulus}
    (certificates : List LogicalRowCertificate) (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads)) : Accepted (nativeView trace) := by
  refine ⟨?_, ?_, states, memory⟩
  · intro row member
    change row ∈ trace.rows at member
    rw [rowBinding] at member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
    exact row_native_constraints cert
  · intro row member
    change row ∈ trace.rows at member
    rw [rowBinding] at member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
    exact row_active cert

theorem accepted_and_decoded {trace : UnifiedTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads)) :
    Accepted trace ∧ UnifiedReduced.Decoded trace NativeDecoder.unifiedProgram := by
  have native := native_accepted certificates rowBinding states memory
  have initial : (nativeView trace).initial.word.lo < Arithmetic.limbBase := by
    change trace.initial.word.lo < Arithmetic.limbBase
    rw [boundary.initialPC]
    decide +kernel
  have ranges := NativeDecoder.Proofs.unified_query_pc_low native initial
  have constraints : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom) := by
    intro row member
    have typed := ranges row member
    rw [rowBinding] at member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
    rw [boundary.setup]
    exact row_constraints cert boundary.image typed
  refine ⟨⟨constraints, native.active, states, memory⟩, ?_⟩
  intro row member
  have typed := ranges row member
  rw [rowBinding] at member
  obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
  exact row_decoded cert typed

/-- Actual unified compiler rows with exact physical lookup matching
compose to the retained Sail execution theorem under exact logical matching. -/
theorem native_execution {trace : UnifiedTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    (byteInverse : SerializedInverse.Scale256 babyBearModulus) :
    Realizes (UnifiedReduced.Step NativeDecoder.unifiedProgram) trace before cells (ROMView.token before) := by
  obtain ⟨accepted, decoded⟩ := accepted_and_decoded boundary certificates rowBinding states memory
  exact UnifiedReduced.Proofs.trace_execution (by decide +kernel) inverse byteInverse
    (boot_inputs boundary) accepted decoded

end Airbender.Compiler.UnifiedExecution.Logical


namespace Airbender.Compiler.UnifiedExecution.Logical
open Airbender Airbender.Trace Reference.RiscV.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
theorem program_accepted_and_decoded {trace : UnifiedTrace babyBearModulus}
    {before : State} {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (boundary : ProgramBoundary trace before cells program) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
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
    (boundary : ProgramBoundary trace before cells program) (certificates : List LogicalRowCertificate)
    (rowBinding : trace.rows = certificates.map LogicalRowCertificate.row)
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

end Airbender.Compiler.UnifiedExecution.Logical
