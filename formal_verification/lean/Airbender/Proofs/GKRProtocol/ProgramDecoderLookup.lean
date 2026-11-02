import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.AddSubCached
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.JumpBranchCached
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.MulDivCached
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.WordMemoryCached
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.UnifiedCached
import Airbender.Proofs.GKRProtocol.ProgramLogicalRows

namespace Airbender.Compiler
open Airbender.Trace Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

namespace PooledExecution

theorem ProgramLogicalRowCertificate.decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (cert : ProgramLogicalRowCertificate (unrolledLookupRows initial columns))
    (typed : cert.row.decoderQuery[0].val < 65536) :
    ProgramRows.maskRow (masks cert.row.family) cert.row.decoderQuery ∈ columns cert.row.family := by
  cases cert with
  | addSubCached input arguments => exact ProgramDecoderLookup.AddSubCached.decoder_lookup setup input arguments typed
  | jumpBranchCached input arguments => exact ProgramDecoderLookup.JumpBranchCached.decoder_lookup setup input arguments typed
  | mulDivCached input arguments => exact ProgramDecoderLookup.MulDivCached.decoder_lookup setup input arguments typed
  | shiftBinopCached input arguments => exact ProgramDecoderLookup.ShiftBinopCached.decoder_lookup setup input arguments typed
  | wordMemoryCached input arguments => exact ProgramDecoderLookup.WordMemoryCached.decoder_lookup setup input arguments typed
  | subwordMemoryCached input arguments => exact ProgramDecoderLookup.SubwordMemoryCached.decoder_lookup setup input arguments typed

/-- Derive the public decoder matching premise from actual row certificates.
Native state and constraint proofs must supply the PC range. -/
theorem decoder_exact_lookup [Fact babyBearModulus.Prime]
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (certs : List (ProgramLogicalRowCertificate (unrolledLookupRows initial columns)))
    (trace : PooledTrace babyBearModulus)
    (rows : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (typed : ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536) :
    UnrolledDecoderExactLookup trace masks columns := by
  intro row member
  have certified : row ∈ certs.map ProgramLogicalRowCertificate.row := rows ▸ member
  obtain ⟨cert, _, equal⟩ := List.mem_map.mp certified
  subst row
  exact cert.decoder_lookup setup (typed cert.row member)

end PooledExecution

namespace UnifiedExecution

theorem ProgramLogicalRowCertificate.decoder_lookup
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (cert : ProgramLogicalRowCertificate (unifiedLookupRows initial columns))
    (typed : cert.row.decoderQuery[0].val < 65536) :
    ProgramRows.maskRow mask cert.row.decoderQuery ∈ columns := by
  cases cert with
  | unifiedCached input arguments => exact ProgramDecoderLookup.UnifiedCached.decoder_lookup setup input arguments typed

theorem decoder_exact_lookup [Fact babyBearModulus.Prime]
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (certs : List (ProgramLogicalRowCertificate (unifiedLookupRows initial columns)))
    (trace : UnifiedTrace babyBearModulus)
    (rows : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (typed : ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536) :
    UnifiedDecoderExactLookup trace mask columns := by
  intro row member
  have certified : row ∈ certs.map ProgramLogicalRowCertificate.row := rows ▸ member
  obtain ⟨cert, _, equal⟩ := List.mem_map.mp certified
  subst row
  exact cert.decoder_lookup setup (typed cert.row member)

end UnifiedExecution
end Airbender.Compiler
