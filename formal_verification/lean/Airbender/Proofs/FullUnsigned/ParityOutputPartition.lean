import Airbender.Proofs.FullUnsigned.SourceIndexPartitions
import Airbender.Proofs.FullUnsigned.Source.Parity
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_source_partition Airbender.Setup.ParityOutputPartition
  from Airbender.Setup.SourceCaptureParity.entries_3282
  chunk_counts [10, 1657, 1661, 1661, 1657, 1657, 1661, 1661, 1657, 1657, 1660, 1659, 1658, 1657, 1658, 1663, 1658, 1660, 1658, 1657, 1658, 1663, 1658, 1657, 1661, 1662, 1657, 1657, 1660, 1659, 1660, 1657, 1660, 1658, 1660, 1657, 1660, 1662, 1657, 1657, 1660, 1661, 1658, 1657, 1661, 1660, 1658, 1657, 1658, 1662, 1658, 1663, 1658, 1657, 1661, 1659, 1658, 1657, 1660, 1662, 1657, 1657, 1660, 1659, 1660, 1, 1]
