import Slop.KeccakSplit.Interface
import Slop.KeccakSplit.ColumnParity.Execution
import Slop.KeccakSplit.ThetaRho.Execution
import Slop.KeccakSplit.Chi5.Execution

/- The per-row circuit contract of the three split Keccak workers, over BabyBear and
   the exported setups. -/

namespace Airbender.Keccak.Split.Native.Proofs
set_option warningAsError true

theorem row_facts : RowFacts where
  writes := by
    intro row h active reads
    cases row with
    | mk kind w =>
      cases kind
      · exact ColumnParity.Proofs.writes w h active reads
      · exact ThetaRho.Proofs.writes w h active reads
      · exact Chi5.Proofs.writes w h active reads
  effects := by
    intro row h active reads
    cases row with
    | mk kind w =>
      cases kind
      · exact ColumnParity.Proofs.effects w h active
      · exact ThetaRho.Proofs.effects w h active reads
      · exact Chi5.Proofs.effects w h active
  aligned := by
    intro row h
    cases row with
    | mk kind w =>
      cases kind
      · exact ColumnParity.Proofs.pointer_aligned_word w h
      · exact ThetaRho.Proofs.pointer_aligned_word w h
      · exact Chi5.Proofs.pointer_aligned_word w h
  addresses := by
    intro row index h active control pointerBound
    cases row with
    | mk kind w =>
      cases kind
      · exact ColumnParity.Proofs.addresses w index h active control pointerBound
      · exact ThetaRho.Proofs.addresses w index h active control pointerBound
      · exact Chi5.Proofs.addresses w index h active control pointerBound

end Airbender.Keccak.Split.Native.Proofs
