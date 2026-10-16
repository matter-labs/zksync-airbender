import Airbender.Proofs.Keccak.ControllerCertificateBase

namespace Airbender.Keccak.Controller.Proofs.Certificate
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

keccak_controller_certificate piece0 4 0
keccak_controller_certificate piece1 4 1
keccak_controller_certificate piece2 4 2
keccak_controller_certificate piece3 4 3
keccak_controller_certificate piece4 4 4
keccak_controller_certificate piece5 4 5
keccak_controller_certificate piece6 4 6
keccak_controller_certificate piece7 4 7

private theorem pieces (chunk : Fin 8) : ControllerPiece 4 chunk := by
  fin_cases chunk
  · exact piece0
  · exact piece1
  · exact piece2
  · exact piece3
  · exact piece4
  · exact piece5
  · exact piece6
  · exact piece7

/-- Imported native controller field 4, checked over every key. -/
theorem field4 (high low : Fin 64) :
    (rows (splitKey high low))[(4 : Fin 6)] =
      (referenceRows (splitKey high low))[(4 : Fin 6)] :=
  field_of_pieces 4 pieces high low

end Airbender.Keccak.Controller.Proofs.Certificate
