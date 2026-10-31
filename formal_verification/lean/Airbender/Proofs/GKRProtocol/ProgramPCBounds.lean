import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.AddSubCached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.JumpBranchUncached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.MulDivCached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.ProgramPCLowNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup

namespace Airbender.Compiler
open Airbender.Trace Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

namespace PooledExecution

theorem ProgramLogicalRowCertificate.final_pc_low
    (decoder : Configuration → List (List Source.BaseField)) (wordAt : Nat → BitVec 32)
    (setup : PooledSetup babyBearModulus) (cert : ProgramLogicalRowCertificate (NativeProgramSetup.rows decoder wordAt)) :
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
  | subwordMemoryUncached input arguments => exact ProgramPCLowNative.SubwordMemoryUncached.final_pc_low decoder wordAt input arguments
  | subwordMemoryCached input arguments => exact ProgramPCLowNative.SubwordMemoryCached.final_pc_low decoder wordAt input arguments

/-- Exact state matching carries native output ranges to every decoder query. -/
theorem native_query_pc_low
    (decoder : Configuration → List (List Source.BaseField)) (wordAt : Nat → BitVec 32)
    (certs : List (ProgramLogicalRowCertificate (NativeProgramSetup.rows decoder wordAt)))
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
    exact ProgramLogicalRowCertificate.final_pc_low decoder wordAt trace.rom cert
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
theorem decoder_exact_lookup_from_native [Fact babyBearModulus.Prime]
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (certs : List (ProgramLogicalRowCertificate (unrolledLookupRows initial columns)))
    (trace : PooledTrace babyBearModulus)
    (rowsEq : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initialBound : trace.initial.word.lo < 65536) : UnrolledDecoderExactLookup trace masks columns :=
  decoder_exact_lookup setup certs trace rowsEq
    (native_query_pc_low (unrolledDecoderColumns columns) (ROM.words initial) certs trace rowsEq states initialBound)

end PooledExecution

namespace UnifiedExecution

theorem ProgramLogicalRowCertificate.final_pc_low
    (decoder : Configuration → List (List Source.BaseField)) (wordAt : Nat → BitVec 32)
    (cert : ProgramLogicalRowCertificate (NativeProgramSetup.rows decoder wordAt)) :
    cert.row.finish.word.lo < 65536 := by
  cases cert with
  | unifiedUncached input arguments => exact ProgramPCLowNative.UnifiedUncached.final_pc_low decoder wordAt input arguments
  | unifiedCached input arguments => exact ProgramPCLowNative.UnifiedCached.final_pc_low decoder wordAt input arguments

/-- Exact state matching carries native output ranges to every decoder query. -/
theorem native_query_pc_low
    (decoder : Configuration → List (List Source.BaseField)) (wordAt : Nat → BitVec 32)
    (certs : List (ProgramLogicalRowCertificate (NativeProgramSetup.rows decoder wordAt)))
    (trace : UnifiedTrace babyBearModulus)
    (rowsEq : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initial : trace.initial.word.lo < 65536) :
    ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536 := by
  have outputs : ∀ row ∈ trace.rows, row.finish.word.lo < 65536 := by
    intro row member
    have certified : row ∈ certs.map ProgramLogicalRowCertificate.row := rowsEq ▸ member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp certified
    exact ProgramLogicalRowCertificate.final_pc_low decoder wordAt cert
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
    cases family
    exact incoming

/-- Derive public decoder matching without a per-row typing premise. -/
theorem decoder_exact_lookup_from_native [Fact babyBearModulus.Prime]
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (certs : List (ProgramLogicalRowCertificate (unifiedLookupRows initial columns)))
    (trace : UnifiedTrace babyBearModulus)
    (rowsEq : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initialBound : trace.initial.word.lo < 65536) : UnifiedDecoderExactLookup trace mask columns :=
  decoder_exact_lookup setup certs trace rowsEq
    (native_query_pc_low (unifiedDecoderColumns columns) (ROM.words initial) certs trace rowsEq states initialBound)

end UnifiedExecution

end Airbender.Compiler
