import GKRProtocol.CacheNative.AddSubCached

namespace Tests.GKRCacheBindings
open Airbender Airbender.Compiler
open Airbender.Compiler.CacheNative.AddSubCached
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def challenges : CacheChallenges Source.BaseField :=
  ⟨2, 17, fun index => [3, 5, 7, 11, 13, 19][index.val]!⟩

private def identity := RingHom.id Source.BaseField

/-- The actual second register write increments the low timestamp by one. -/
theorem preserves_write_timestamp_offset :
    (native.cache3 identity challenges).program.value (fun _ => 0) = 24 := by decide +kernel

/-- The PC cell has the native special address space 2. -/
theorem preserves_pc_address_space :
    (native.cache5 identity challenges).program.value (fun _ => 0) = 19 := by decide +kernel

/-- The scalar timestamp lookup uses a decoded coefficient of 2^19. -/
theorem decodes_scalar_coefficient :
    (native.cache8 identity challenges).program.value
      (fun address => if address = GKRAddress.BaseLayerWitness 16 then 1 else 0) = 524288 := by decide +kernel

/-- The last family-mask bit has weight 2^8 in vector column 7. -/
theorem preserves_packed_vector_column :
    (native.cache14 identity challenges).program.value
      (fun address => if address = GKRAddress.BaseLayerWitness 10 then 1 else 0) = 32768 := by decide +kernel

theorem preserves_setup_column_order :
    (native.cache15 identity challenges).program.value
      (fun address => match address with | .Setup index => index + 1 | _ => 0) = 1793 := by decide +kernel

theorem rejects_changed_dependency :
    ({ native.cache3 identity challenges with
      program := AffineProgram.input (GKRAddress.BaseLayerWitness 999) } : CacheBinding Source.BaseField).portsValid = false := by
  decide +kernel

theorem rejects_free_cache_claim :
    decide ((native.cache3 identity challenges).expectedClaim [3, 4] (fun _ _ => 0) = 25) = false := by
  decide +kernel

end Tests.GKRCacheBindings
