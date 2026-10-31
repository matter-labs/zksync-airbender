import Airbender.Proofs.GKRProtocol.ProgramPCBounds
import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.SubwordMemoryCached

namespace Airbender.Compiler
open Airbender.Trace Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

namespace PooledExecution

theorem ProgramLogicalRowCertificate.program_decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (cert : ProgramLogicalRowCertificate (unrolledProgramLookupRows initial columns))
    (typed : cert.row.decoderQuery[0].val < 65536) :
    ProgramRows.maskRow (masks cert.row.family) cert.row.decoderQuery ∈ columns cert.row.family := by
  cases cert with
  | addSubUncached input arguments => exact ProgramDecoderLookup.AddSubUncached.decoder_lookup setup input arguments typed
  | addSubCached input arguments => exact ProgramDecoderLookup.AddSubCached.decoder_lookup setup input arguments typed
  | jumpBranchUncached input arguments => exact ProgramDecoderLookup.JumpBranchUncached.decoder_lookup setup input arguments typed
  | jumpBranchCached input arguments => exact ProgramDecoderLookup.JumpBranchCached.decoder_lookup setup input arguments typed
  | mulDivUncached input arguments => exact ProgramDecoderLookup.MulDivUncached.decoder_lookup setup input arguments typed
  | mulDivCached input arguments => exact ProgramDecoderLookup.MulDivCached.decoder_lookup setup input arguments typed
  | shiftBinopUncached input arguments => exact ProgramDecoderLookup.ShiftBinopUncached.decoder_lookup setup input arguments typed
  | shiftBinopCached input arguments => exact ProgramDecoderLookup.ShiftBinopCached.decoder_lookup setup input arguments typed
  | wordMemoryUncached input arguments => exact ProgramDecoderLookup.WordMemoryUncached.decoder_lookup setup input arguments typed
  | wordMemoryCached input arguments => exact ProgramDecoderLookup.WordMemoryCached.decoder_lookup setup input arguments typed
  | subwordMemoryUncached input arguments => exact ProgramConstraintsNative.SubwordMemoryUncached.decoder_lookup setup input arguments typed
  | subwordMemoryCached input arguments => exact ProgramConstraintsNative.SubwordMemoryCached.decoder_lookup setup input arguments typed

/-- Derive the public decoder matching premise from actual row certificates.
Native state and constraint proofs must supply the PC range. -/
theorem program_decoder_exact_lookup [Fact babyBearModulus.Prime]
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (certs : List (ProgramLogicalRowCertificate (unrolledProgramLookupRows initial columns)))
    (trace : PooledTrace babyBearModulus)
    (rows : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (typed : ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536) :
    UnrolledDecoderExactLookup trace masks columns := by
  intro row member
  have certified : row ∈ certs.map ProgramLogicalRowCertificate.row := rows ▸ member
  obtain ⟨cert, _, equal⟩ := List.mem_map.mp certified
  subst row
  exact cert.program_decoder_lookup setup (typed cert.row member)

end PooledExecution

namespace PooledExecution

theorem ProgramLogicalRowCertificate.program_final_pc_low
    (decoder : Configuration → List (List Source.BaseField)) (wordAt : Nat → BitVec 32)
    (setup : PooledSetup babyBearModulus) (cert : ProgramLogicalRowCertificate (NativeProgramSetup.programRows decoder wordAt)) :
    cert.row.finish.word.lo < 65536 := by
  cases cert with
  | addSubUncached input arguments => exact ProgramPCLowNative.AddSubUncached.final_pc_low decoder wordAt input arguments setup
  | addSubCached input arguments => exact ProgramPCLowNative.AddSubCached.final_pc_low decoder wordAt input arguments setup
  | jumpBranchUncached input arguments => exact ProgramPCLowNative.JumpBranchUncached.final_pc_low decoder wordAt input arguments setup
  | jumpBranchCached input arguments => exact ProgramPCLowNative.JumpBranchCached.final_pc_low decoder wordAt input arguments setup
  | mulDivUncached input arguments => exact ProgramPCLowNative.MulDivUncached.final_pc_low decoder wordAt input arguments setup
  | mulDivCached input arguments => exact ProgramPCLowNative.MulDivCached.final_pc_low decoder wordAt input arguments setup
  | shiftBinopUncached input arguments => exact ProgramPCLowNative.ShiftBinopUncached.final_pc_low decoder wordAt input arguments
  | shiftBinopCached input arguments => exact ProgramPCLowNative.ShiftBinopCached.final_pc_low decoder wordAt input arguments
  | wordMemoryUncached input arguments => exact ProgramPCLowNative.WordMemoryUncached.final_pc_low decoder wordAt input arguments
  | wordMemoryCached input arguments => exact ProgramPCLowNative.WordMemoryCached.final_pc_low decoder wordAt input arguments
  | subwordMemoryUncached input arguments => exact ProgramConstraintsNative.SubwordMemoryUncached.final_pc_low decoder wordAt input arguments
  | subwordMemoryCached input arguments => exact ProgramConstraintsNative.SubwordMemoryCached.final_pc_low decoder wordAt input arguments

/-- Exact state matching carries native output ranges to every decoder query. -/
theorem program_native_query_pc_low
    (decoder : Configuration → List (List Source.BaseField)) (wordAt : Nat → BitVec 32)
    (certs : List (ProgramLogicalRowCertificate (NativeProgramSetup.programRows decoder wordAt)))
    (trace : PooledTrace babyBearModulus)
    (rowsEq : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initial : trace.initial.word.lo < 65536) :
    ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536 := by
  have outputs : ∀ row ∈ trace.rows, row.finish.word.lo < 65536 := by
    intro row member
    have certified : row ∈ certs.map ProgramLogicalRowCertificate.row := rowsEq ▸ member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp certified
    exact ProgramLogicalRowCertificate.program_final_pc_low decoder wordAt trace.rom cert
  intro row member
  have incoming : row.start.word.lo < 65536 := by
    have matched := states.mem_iff.mpr
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
    rcases List.mem_cons.mp matched with same | previous
    · exact same ▸ initial
    · obtain ⟨previous, present, equal⟩ := List.mem_map.mp previous
      exact equal ▸ outputs previous present
  cases row with
  | mk family assignment =>
    cases family <;> exact incoming

/-- Derive public decoder matching without a per-row typing premise. -/
theorem program_decoder_exact_lookup_from_native [Fact babyBearModulus.Prime]
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (certs : List (ProgramLogicalRowCertificate (unrolledProgramLookupRows initial columns)))
    (trace : PooledTrace babyBearModulus)
    (rowsEq : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initialBound : trace.initial.word.lo < 65536) : UnrolledDecoderExactLookup trace masks columns :=
  program_decoder_exact_lookup setup certs trace rowsEq
    (program_native_query_pc_low (unrolledDecoderColumns columns) (ROM.words initial) certs trace rowsEq states initialBound)

end PooledExecution

end Airbender.Compiler
