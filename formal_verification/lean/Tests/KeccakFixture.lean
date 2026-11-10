import Airbender.Proofs.Constraints
import Airbender.Proofs.BabyBear

namespace Tests.Keccak
open Airbender

-- A deliberately permissive fixed setup isolates the structural guarantees.
-- These tests do not establish the semantics of the XOR/ANDN/rotation tables.
def permissiveSetup : Table (ZMod babyBearModulus) (fields 8) where
  name := "StructuralTestsOnly"
  Contains _ _ := True

end Tests.Keccak
