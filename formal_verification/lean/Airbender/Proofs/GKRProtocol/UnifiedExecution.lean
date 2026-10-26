import Airbender.Review.Compiler.Unified
import Airbender.Proofs.GKRProtocol.UnifiedRowNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.UnifiedRowNative.UnifiedCached
import Airbender.Proofs.Tables.DecoderPCLow
import Airbender.Proofs.UnifiedReduced.Composition

namespace Airbender.Compiler.UnifiedExecution
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable abbrev nativeSetup := CleanClosedNative.UnifiedUncached.nativeSetup

noncomputable def nativeView (trace : UnifiedTrace babyBearModulus) : UnifiedTrace babyBearModulus :=
  { trace with rom := nativeSetup }

theorem row_active (cert : RowCertificate) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
  | plain cert => exact UnifiedRowNative.UnifiedUncached.active cert
  | preprocessed cert => exact UnifiedRowNative.UnifiedCached.active cert

theorem row_native_constraints (cert : RowCertificate) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints nativeSetup) := by
  cases cert with
  | plain cert => exact UnifiedRowNative.UnifiedUncached.native_constraints cert
  | preprocessed cert => exact UnifiedRowNative.UnifiedCached.native_constraints cert

theorem row_constraints (cert : RowCertificate) {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) (typed : cert.row.decoderQuery[0].val < 65536) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints (UnifiedReduced.Setup.table before)) := by
  cases cert with
  | plain cert => exact UnifiedRowNative.UnifiedUncached.constraints cert image typed
  | preprocessed cert => exact UnifiedRowNative.UnifiedCached.constraints cert image typed

theorem row_decoded (cert : RowCertificate) (typed : cert.row.decoderQuery[0].val < 65536) :
    (decoderTable NativeDecoder.unifiedProgram cert.row.family).Contains #[] cert.row.decoderQuery := by
  cases cert with
  | plain cert => exact UnifiedRowNative.UnifiedUncached.decoded cert typed
  | preprocessed cert => exact UnifiedRowNative.UnifiedCached.decoded cert typed

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
    (certificates : List RowCertificate) (rowBinding : trace.rows = certificates.map RowCertificate.row)
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
    (boundary : PublicBoundary trace before cells) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
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

/-- Actual unified compiler frames, including arbitrary initialization windows,
compose to the retained Sail execution theorem under exact logical matching. -/
theorem native_execution {trace : UnifiedTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
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

end Airbender.Compiler.UnifiedExecution
