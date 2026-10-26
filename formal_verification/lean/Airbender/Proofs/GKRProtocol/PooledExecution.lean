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

namespace Airbender.Compiler.PooledExecution
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem row_active (cert : RowCertificate) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
  | addSubUncached cert => exact PooledRowNative.AddSubUncached.active cert
  | addSubCached cert => exact PooledRowNative.AddSubCached.active cert
  | jumpBranchUncached cert => exact PooledRowNative.JumpBranchUncached.active cert
  | jumpBranchCached cert => exact PooledRowNative.JumpBranchCached.active cert
  | mulDivUncached cert => exact PooledRowNative.MulDivUncached.active cert
  | mulDivCached cert => exact PooledRowNative.MulDivCached.active cert
  | shiftBinopUncached cert => exact PooledRowNative.ShiftBinopUncached.active cert
  | shiftBinopCached cert => exact PooledRowNative.ShiftBinopCached.active cert
  | wordMemoryUncached cert => exact PooledRowNative.WordMemoryUncached.active cert
  | wordMemoryCached cert => exact PooledRowNative.WordMemoryCached.active cert
  | subwordMemoryUncached cert => exact PooledRowNative.SubwordMemoryUncached.active cert
  | subwordMemoryCached cert => exact PooledRowNative.SubwordMemoryCached.active cert

theorem row_constraints (cert : RowCertificate) {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) {cells : List Cell}
    {tokens : List (MemoryToken babyBearModulus)}
    (physical : initialImage before cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints (⟨ROM.table cells tokens,
        Verification.subwordTable (ROM.words before)⟩ : PooledSetup babyBearModulus)) := by
  cases cert with
  | addSubUncached cert => exact PooledRowNative.AddSubUncached.constraints cert image physical domain
  | addSubCached cert => exact PooledRowNative.AddSubCached.constraints cert image physical domain
  | jumpBranchUncached cert => exact PooledRowNative.JumpBranchUncached.constraints cert image physical domain
  | jumpBranchCached cert => exact PooledRowNative.JumpBranchCached.constraints cert image physical domain
  | mulDivUncached cert => exact PooledRowNative.MulDivUncached.constraints cert image physical domain
  | mulDivCached cert => exact PooledRowNative.MulDivCached.constraints cert image physical domain
  | shiftBinopUncached cert => exact PooledRowNative.ShiftBinopUncached.constraints cert image physical domain
  | shiftBinopCached cert => exact PooledRowNative.ShiftBinopCached.constraints cert image physical domain
  | wordMemoryUncached cert => exact PooledRowNative.WordMemoryUncached.constraints cert image physical domain
  | wordMemoryCached cert => exact PooledRowNative.WordMemoryCached.constraints cert image physical domain
  | subwordMemoryUncached cert => exact PooledRowNative.SubwordMemoryUncached.constraints cert image physical domain
  | subwordMemoryCached cert => exact PooledRowNative.SubwordMemoryCached.constraints cert image physical domain

theorem row_decoded (cert : RowCertificate)
    (typed : cert.row.decoderQuery[0].val < 65536) :
    (decoderTable NativeDecoder.pooledProgram cert.row.family).Contains #[]
      cert.row.decoderQuery := by
  cases cert with
  | addSubUncached cert => exact PooledRowNative.AddSubUncached.decoded cert typed
  | addSubCached cert => exact PooledRowNative.AddSubCached.decoded cert typed
  | jumpBranchUncached cert => exact PooledRowNative.JumpBranchUncached.decoded cert typed
  | jumpBranchCached cert => exact PooledRowNative.JumpBranchCached.decoded cert typed
  | mulDivUncached cert => exact PooledRowNative.MulDivUncached.decoded cert typed
  | mulDivCached cert => exact PooledRowNative.MulDivCached.decoded cert typed
  | shiftBinopUncached cert => exact PooledRowNative.ShiftBinopUncached.decoded cert typed
  | shiftBinopCached cert => exact PooledRowNative.ShiftBinopCached.decoded cert typed
  | wordMemoryUncached cert => exact PooledRowNative.WordMemoryUncached.decoded cert typed
  | wordMemoryCached cert => exact PooledRowNative.WordMemoryCached.decoded cert typed
  | subwordMemoryUncached cert => exact PooledRowNative.SubwordMemoryUncached.decoded cert typed
  | subwordMemoryCached cert => exact PooledRowNative.SubwordMemoryCached.decoded cert typed

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

/-- Native equations and source-frame lookup validity construct acceptance.
Exact state and RAM matching remain logical argument-boundary premises. -/
theorem accepted {trace : PooledTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
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
    (certificates : List RowCertificate) (rowBinding : trace.rows = certificates.map RowCertificate.row)
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
    (boundary : PublicBoundary trace before cells) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
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

end Airbender.Compiler.PooledExecution
