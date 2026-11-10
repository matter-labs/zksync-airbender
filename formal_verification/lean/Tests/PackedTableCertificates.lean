import Airbender.Proofs.Tables.PackedBlockCertificate

namespace Tests.PackedTableCertificates
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true

theorem first_nonzero_byte :
    PackedBlockCertificate.check 257 [.dense 1 1] = true := by decide +kernel

theorem changed_byte_rejected :
    PackedBlockCertificate.check 257 [.dense 1 0] = false := by decide +kernel

theorem little_endian_payload :
    PackedBlockCertificate.check 256 [.dense 2 256] = true := by decide +kernel

theorem reversed_bytes_rejected :
    PackedBlockCertificate.check 256 [.dense 2 1] = false := by decide +kernel

theorem extra_payload_byte_rejected :
    PackedBlockCertificate.check 256 [.dense 2 65792] = false := by decide +kernel

theorem periodic_source :
    PackedBlockCertificate.check 256 [.periodic 2 (.ofNat 1) 1 0] = true := by decide +kernel

theorem affine_source :
    PackedBlockCertificate.check 256 [.affine 2 0 (.ofNat 1)] = true := by decide +kernel

theorem row_boundary :
    PackedBlockCertificate.check 255 [.dense 2 0] = true := by decide +kernel

theorem last_source_byte :
    PackedBlockCertificate.check 65535 [.dense 1 255] = true := by decide +kernel

theorem outside_table_rejected :
    PackedBlockCertificate.check 65536 [.dense 1 0] = false := by decide +kernel

end Tests.PackedTableCertificates
