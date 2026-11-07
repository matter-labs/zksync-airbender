import Airbender.Proofs.Bigint.ImportedSetup

namespace Airbender.Bigint.Proofs
set_option warningAsError true
set_option Elab.async false

def lookupReferenceRow (index : Fin 1390592) : Nat × Nat × Nat :=
  if index.val < 262144 then (index.val / 512, index.val % 512, 22)
  else if index.val < 1310720 then ((index.val - 262144) / 1024, (index.val - 262144) % 1024, 23)
  else if index.val < 1312768 then (index.val - 1310720, 0, 24)
  else if index.val < 1316864 then (index.val - 1312768, 0, 25)
  else if index.val < 1325056 then (index.val - 1316864, 0, 26)
  else (index.val - 1325056, (index.val - 1325056) % 256, 41)

theorem setup_lookup_reference_iff {p : Nat} [Fact p.Prime]
    (entry : Vector (Expression (ZMod p)) 3)
    (env : Environment (ZMod p)) :
    (Lookup.mk Bigint.setupTable.toRaw entry).Contains env ↔
      ∃ i : Fin 1390592, entry.map (Expression.eval env) =
        #v[((lookupReferenceRow i).1 : ZMod p),
          ((lookupReferenceRow i).2.1 : ZMod p),
          ((lookupReferenceRow i).2.2 : ZMod p)] := by
  change (∃ i : Fin 1390592, entry.map (Expression.eval env) =
        #v[((Bigint.setupRow i).1 : ZMod p),
          ((Bigint.setupRow i).2.1 : ZMod p),
          ((Bigint.setupRow i).2.2 : ZMod p)]) ↔ _
  simp only [Bigint.Proofs.setup_row_characterization, lookupReferenceRow]


end Airbender.Bigint.Proofs
