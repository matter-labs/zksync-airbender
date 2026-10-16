import Airbender.Proofs.Keccak.ControllerCertificateBase

namespace Airbender.Keccak.Controller.Proofs.Certificate
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

keccak_controller_certificate piece0 1 0
keccak_controller_certificate piece1 1 1
keccak_controller_certificate piece2 1 2
keccak_controller_certificate piece3 1 3
keccak_controller_certificate piece4 1 4
keccak_controller_certificate piece5 1 5
keccak_controller_certificate piece6 1 6
keccak_controller_certificate piece7 1 7

private theorem pieces (chunk : Fin 8) : ControllerPiece 1 chunk := by
  fin_cases chunk
  · exact piece0
  · exact piece1
  · exact piece2
  · exact piece3
  · exact piece4
  · exact piece5
  · exact piece6
  · exact piece7

/-- Imported native controller field 1, checked over every key. -/
theorem field1 (high low : Fin 64) :
    (rows (splitKey high low))[(1 : Fin 6)] =
      (referenceRows (splitKey high low))[(1 : Fin 6)] :=
  field_of_pieces 1 pieces high low

end Airbender.Keccak.Controller.Proofs.Certificate
