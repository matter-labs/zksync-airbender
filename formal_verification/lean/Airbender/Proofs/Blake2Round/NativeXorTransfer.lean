import Airbender.Proofs.Blake2Round.NativeMembership
import Airbender.Proofs.Blake2Round.NativeGAssignment
import Airbender.Proofs.Blake2Round.GQueryTable

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

def plainBase : Vector Nat 3 := #v[256, 128, 512]
def plainTags : Vector Nat 3 := #v[4, 19, 20]
def plainGKind : Vector (Fin 5) 3 := #v[0, 3, 4]
def carryTags : Vector Nat 2 := #v[55, 56]
def carryGKind : Vector (Fin 5) 2 := #v[0, 3]

def plainPad {p : Nat} (row : Vector (ZMod p) 6) : Vector (ZMod p) 9 :=
  #v[row[0], row[1], row[2], 0, 0, 0, 0, 0, row[5]]

def carryPad {p : Nat} (kind : Fin 2) (row : Vector (ZMod p) 6) : Vector (ZMod p) 9 :=
  #v[row[0], row[1], row[3], 0, 0, 0, 0, 0, ((#v[4, 19][kind] : Nat) : ZMod p)]

private theorem plain_payload {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {source : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)}
    (kind : Fin 3) (member : (Lookup.mk setupTable.toRaw source).Contains env)
    (selected : source[5].eval env = ((plainTags[kind] : Nat) : ZMod p)) :
    ∃ n, n < nativeLengths[(⟨kind.val, by omega⟩ : Fin 6)] ∧
      source.map (Expression.eval env) =
        (plainXorRow plainBase[kind] plainTags[kind] n).map (fun value : Nat => (value : ZMod p)) := by
  have tag : nativeTags[(⟨kind.val, by omega⟩ : Fin 6)] = plainTags[kind] := by fin_cases kind <;> rfl
  obtain ⟨n, bound, row⟩ := selected_region hp ⟨kind.val, by omega⟩ member (by rw [tag]; exact selected)
  have reference : referenceRegionRow ⟨kind.val, by omega⟩ n =
      plainXorRow plainBase[kind] plainTags[kind] n := by fin_cases kind <;> rfl
  exact ⟨n, bound, reference ▸ row⟩

private theorem carry_payload {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {source : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)}
    (kind : Fin 2) (member : (Lookup.mk setupTable.toRaw source).Contains env)
    (selected : source[5].eval env = ((carryTags[kind] : Nat) : ZMod p)) :
    ∃ n, n < nativeLengths[carryKind kind] ∧
      source.map (Expression.eval env) =
        (carryXorRow (carryBase kind) carryTags[kind] n).map (fun value : Nat => (value : ZMod p)) := by
  have tag : nativeTags[carryKind kind] = carryTags[kind] := by fin_cases kind <;> rfl
  obtain ⟨n, bound, row⟩ := selected_region hp (carryKind kind) member (by rw [tag]; exact selected)
  have reference : referenceRegionRow (carryKind kind) n =
      carryXorRow (carryBase kind) carryTags[kind] n := by fin_cases kind <;> rfl
  exact ⟨n, bound, reference ▸ row⟩

/-- The carry limit follows from the actual extra input column of membership. -/
theorem carry_value_bound {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {source : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)}
    (kind : Fin 2) (member : (Lookup.mk setupTable.toRaw source).Contains env)
    (selected : source[5].eval env = ((carryTags[kind] : Nat) : ZMod p)) :
    (source[2].eval env).val < 3 := by
  obtain ⟨n, bound, row⟩ := carry_payload hp kind member selected
  have small : n / (carryBase kind * carryBase kind) < 3 := by
    fin_cases kind <;> norm_num [carryBase, carryKind, nativeLengths] at bound ⊢ <;> omega
  have column : source[2].eval env = ((n / (carryBase kind * carryBase kind) : Nat) : ZMod p) := by
    have same := congrArg (fun v : Vector (ZMod p) 6 => v[2]) row
    simpa [carryXorRow] using same
  rw [column, ZMod.val_natCast_of_lt (by omega)]
  exact small

/-- Reuse an ordinary G lookup through the native plain six-column region. -/
theorem plain_membership {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    (control : Fin 512 → Vector Nat 7)
    {source : Vector (Expression (ZMod p)) 6} {target : Vector (Expression (ZMod p)) 9}
    {sourceEnv targetEnv : Environment (ZMod p)}
    (kind : Fin 3) (member : (Lookup.mk setupTable.toRaw source).Contains sourceEnv)
    (selected : source[5].eval sourceEnv = ((plainTags[kind] : Nat) : ZMod p))
    (columns : target.map (Expression.eval targetEnv) = plainPad (source.map (Expression.eval sourceEnv))) :
    (Lookup.mk (Blake2G.setupTable control).toRaw target).Contains targetEnv := by
  obtain ⟨n, bound, row⟩ := plain_payload hp kind member selected
  apply g_xor_membership control plainGKind[kind] (n / plainBase[kind]) (n % plainBase[kind])
  · fin_cases kind <;> norm_num [plainGKind, plainBase, gWidths, nativeLengths] at bound ⊢ <;> omega
  · fin_cases kind <;> norm_num [plainGKind, plainBase, gWidths] <;> omega
  · rw [columns, row]
    fin_cases kind <;> simp [plainPad, plainXorRow, plainBase, plainTags, plainGKind, gTags]

/-- Forgetting the bounded carry column recovers the unchanged G XOR query. -/
theorem carry_membership {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    (control : Fin 512 → Vector Nat 7)
    {source : Vector (Expression (ZMod p)) 6} {target : Vector (Expression (ZMod p)) 9}
    {sourceEnv targetEnv : Environment (ZMod p)}
    (kind : Fin 2) (member : (Lookup.mk setupTable.toRaw source).Contains sourceEnv)
    (selected : source[5].eval sourceEnv = ((carryTags[kind] : Nat) : ZMod p))
    (columns : target.map (Expression.eval targetEnv) = carryPad kind (source.map (Expression.eval sourceEnv))) :
    (Lookup.mk (Blake2G.setupTable control).toRaw target).Contains targetEnv := by
  obtain ⟨n, bound, row⟩ := carry_payload hp kind member selected
  apply g_xor_membership control carryGKind[kind]
    (n / carryBase kind % carryBase kind) (n % carryBase kind)
  · fin_cases kind <;> norm_num [carryGKind, carryBase, gWidths] <;> omega
  · fin_cases kind <;> norm_num [carryGKind, carryBase, gWidths] <;> omega
  · rw [columns, row]
    fin_cases kind <;> simp [carryPad, carryXorRow, carryBase, carryGKind, gTags]

end Airbender.Blake2Round.Proofs
