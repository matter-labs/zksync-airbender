import Airbender.Proofs.Keccak.ControllerCertificateBase

namespace Airbender.Keccak.Controller.Proofs.Certificate
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

keccak_controller_certificate piece0 5 0
keccak_controller_certificate piece1 5 1
keccak_controller_certificate piece2 5 2
keccak_controller_certificate piece3 5 3
keccak_controller_certificate piece4 5 4
keccak_controller_certificate piece5 5 5
keccak_controller_certificate piece6 5 6
keccak_controller_certificate piece7 5 7

private theorem pieces (chunk : Fin 8) : ControllerPiece 5 chunk := by
  fin_cases chunk
  · exact piece0
  · exact piece1
  · exact piece2
  · exact piece3
  · exact piece4
  · exact piece5
  · exact piece6
  · exact piece7

/-- Imported native controller field 5, checked over every key. -/
theorem field5 (high low : Fin 64) :
    (rows (splitKey high low))[(5 : Fin 6)] =
      (referenceRows (splitKey high low))[(5 : Fin 6)] :=
  field_of_pieces 5 pieces high low

end Airbender.Keccak.Controller.Proofs.Certificate
