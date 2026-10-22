import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Tables.DecoderPCLow
import Airbender.Review.Helpers.Decoder.ImportedPooled
import Airbender.Proofs.Tables.Decoder.AddSub
import Airbender.Proofs.Tables.Decoder.JumpBranch
import Airbender.Proofs.Tables.Decoder.MulDiv
import Airbender.Proofs.Tables.Decoder.ShiftBinop
import Airbender.Proofs.Tables.Decoder.WordMemory
import Airbender.Proofs.Tables.Decoder.Subword

namespace Airbender.Trace.NativeDecoder.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Concrete imported membership supplies every semantic decoder query. The
    guarded PC-limb bounds follow from accepted native constraints and state
    matching; no table-content equivalence, typed-query premise or decoded
    result is assumed. -/
theorem pooled_decoded [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p) {trace : PooledTrace p}
    (accepted : Accepted trace) (initial : trace.initial.word.lo < Arithmetic.limbBase)
    (lookups : PooledLookups trace) :
    PooledDecoded trace pooledProgram := by
  intro row member
  have bounded := pooled_query_pc_low hp accepted initial row member
  have field : 65536 < p := by omega
  have actual := lookups row member
  cases family : row.family
  · exact AddSub.lookup_sound field _ bounded (by simpa only [family, pooledSetup] using actual)
  · exact WordMemory.lookup_sound field _ bounded (by simpa only [family, pooledSetup] using actual)
  · exact JumpBranch.lookup_sound field _ bounded (by simpa only [family, pooledSetup] using actual)
  · exact MulDiv.lookup_sound field _ bounded (by simpa only [family, pooledSetup] using actual)
  · exact ShiftBinop.lookup_sound field _ bounded (by simpa only [family, pooledSetup] using actual)
  · exact Subword.lookup_sound field _ bounded (by simpa only [family, pooledSetup] using actual)

end Airbender.Trace.NativeDecoder.Proofs
