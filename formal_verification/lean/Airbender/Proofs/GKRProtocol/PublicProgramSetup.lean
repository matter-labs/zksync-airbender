import Airbender.Review.Compiler.PublicProgramSetup
import Airbender.Proofs.GKRProtocol.ProgramRows
import Airbender.Proofs.GKRProtocol.UnifiedProgramRows

namespace Airbender.Compiler
open Airbender.Trace Airbender.Trace.NativeDecoder Reference.RiscV.Sail
set_option warningAsError true

/-- An active query in public unrolled setup columns identifies an ordinary
instruction or virtual caller from the supplied text and initial Sail bytes.
Exact circuit lookup matching supplies `member` at the native boundary. -/
theorem unrolled_active_public_source
    {config : ProgramRows.Config} {initial : State} {text : List (BitVec 32)}
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (family : PooledFamily) (query : List (ZMod babyBearModulus))
    (member : query ∈ columns family)
    (bounded : (query.head?.getD 0).val < 65536) :
    ∃ item ∈ ProgramRows.nativeProgramOf config initial text,
      item.Source config initial ∧ item.family = family ∧
        query = ProgramRows.maskRow (masks family) item.query := by
  rw [setup.decoderRows family] at member
  exact ProgramRows.Proofs.native_active_masked_source config initial text
    setup.image setup.size capacity setup.fits family (masks family) query
    member bounded

/-- The same public setup projection for the single unified decoder table. -/
theorem unified_active_public_source
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask}
    {columns : List (List (ZMod babyBearModulus))}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (query : List (ZMod babyBearModulus)) (member : query ∈ columns)
    (bounded : (query.head?.getD 0).val < 65536) :
    ∃ item ∈ UnifiedProgramRows.programOf initial text,
      item.Source initial ∧ query = ProgramRows.maskRow mask item.query := by
  rw [setup.decoderRows] at member
  exact UnifiedProgramRows.Proofs.native_active_masked_source initial text
    setup.image setup.size capacity setup.fits mask query member bounded

end Airbender.Compiler
