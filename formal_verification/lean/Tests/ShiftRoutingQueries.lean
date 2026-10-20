import Tests.ShiftRoutingWitness

namespace Tests.ShiftRoutingQueries
open Airbender Verification ShiftBinop Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Every fixture query uses the actual combined native table. Each witness
    uses an existing checked helper model, without evaluating large native arrays. -/
theorem lookup_members (sample : Fin 24) (slot : Fin 4) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[]
      #v[assignment sample (39 + 4 * slot.val), assignment sample (40 + 4 * slot.val),
         assignment sample (41 + 4 * slot.val), assignment sample (42 + 4 * slot.val)] := by
  fin_cases sample <;> fin_cases slot
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[3,3,0,47]
    apply (native_lookup_scalar .truncate #v[3,3,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨3, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[262143,65528,7,48]
    apply (native_lookup_sll_low #v[262143,65528,7]).mpr
    apply (native_sll_low_membership _).mp
    exact ⟨⟨262143, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[229376,0,0,49]
    apply (native_lookup_sll_high #v[229376,0,0]).mpr
    apply (native_sll_high_membership _).mp
    exact ⟨⟨229376, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0]
    exact (native_lookup_zero #v[0,0,0]).mpr rfl
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[3,3,0,47]
    apply (native_lookup_scalar .truncate #v[3,3,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨3, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[262143,8191,0,50]
    apply (native_lookup_srl_low #v[262143,8191,0]).mpr
    apply (native_srl_low_membership _).mp
    exact ⟨⟨262143, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[229376,0,4096,51]
    apply (native_lookup_srl_high #v[229376,0,4096]).mpr
    apply (native_srl_high_membership _).mp
    exact ⟨⟨229376, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0]
    exact (native_lookup_zero #v[0,0,0]).mpr rfl
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[3,3,0,47]
    apply (native_lookup_scalar .truncate #v[3,3,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨3, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[229376,0,57344,52]
    apply (native_lookup_scalar .signFill #v[229376,0,57344]).mpr
    apply (native_shift_scalar_membership .signFill _).mp
    exact ⟨⟨229376, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[262143,8191,0,50]
    apply (native_lookup_srl_low #v[262143,8191,0]).mpr
    apply (native_srl_low_membership _).mp
    exact ⟨⟨262143, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[229376,0,4096,51]
    apply (native_lookup_srl_high #v[229376,0,4096]).mpr
    apply (native_srl_high_membership _).mp
    exact ⟨⟨229376, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,3,252,4]
    apply (native_lookup_binary .xor #v[255,3,252]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨65283, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,0,255,4]
    apply (native_lookup_binary .xor #v[255,0,255]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨65280, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,4]
    apply (native_lookup_binary .xor #v[0,0,0]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨0, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,0,128,4]
    apply (native_lookup_binary .xor #v[128,0,128]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨32768, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,3,255,6]
    apply (native_lookup_binary .or #v[255,3,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨65283, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,0,255,6]
    apply (native_lookup_binary .or #v[255,0,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨65280, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,6]
    apply (native_lookup_binary .or #v[0,0,0]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨0, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,0,128,6]
    apply (native_lookup_binary .or #v[128,0,128]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨32768, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,3,3,7]
    apply (native_lookup_binary .and #v[255,3,3]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨65283, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,0,0,7]
    apply (native_lookup_binary .and #v[255,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨65280, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,7]
    apply (native_lookup_binary .and #v[0,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨0, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,0,0,7]
    apply (native_lookup_binary .and #v[128,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨32768, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[31,31,0,47]
    apply (native_lookup_scalar .truncate #v[31,31,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨31, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2097151,0,32768,48]
    apply (native_lookup_sll_low #v[2097151,0,32768]).mpr
    apply (native_sll_low_membership _).mp
    exact ⟨⟨2097151, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2064384,0,0,49]
    apply (native_lookup_sll_high #v[2064384,0,0]).mpr
    apply (native_sll_high_membership _).mp
    exact ⟨⟨2064384, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0]
    exact (native_lookup_zero #v[0,0,0]).mpr rfl
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[31,31,0,47]
    apply (native_lookup_scalar .truncate #v[31,31,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨31, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2097151,0,0,50]
    apply (native_lookup_srl_low #v[2097151,0,0]).mpr
    apply (native_srl_low_membership _).mp
    exact ⟨⟨2097151, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2064384,1,0,51]
    apply (native_lookup_srl_high #v[2064384,1,0]).mpr
    apply (native_srl_high_membership _).mp
    exact ⟨⟨2064384, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0]
    exact (native_lookup_zero #v[0,0,0]).mpr rfl
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[1055,31,0,47]
    apply (native_lookup_scalar .truncate #v[1055,31,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨1055, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2064384,65534,65535,52]
    apply (native_lookup_scalar .signFill #v[2064384,65534,65535]).mpr
    apply (native_shift_scalar_membership .signFill _).mp
    exact ⟨⟨2064384, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2097151,0,0,50]
    apply (native_lookup_srl_low #v[2097151,0,0]).mpr
    apply (native_srl_low_membership _).mp
    exact ⟨⟨2097151, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2064384,1,0,51]
    apply (native_lookup_srl_high #v[2064384,1,0]).mpr
    apply (native_srl_high_membership _).mp
    exact ⟨⟨2064384, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,255,0,4]
    apply (native_lookup_binary .xor #v[255,255,0]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨65535, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,255,0,4]
    apply (native_lookup_binary .xor #v[255,255,0]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨65535, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,255,255,4]
    apply (native_lookup_binary .xor #v[0,255,255]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨255, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,255,127,4]
    apply (native_lookup_binary .xor #v[128,255,127]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨33023, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,0,255,6]
    apply (native_lookup_binary .or #v[255,0,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨65280, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,248,255,6]
    apply (native_lookup_binary .or #v[255,248,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨65528, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,255,255,6]
    apply (native_lookup_binary .or #v[0,255,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨255, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,255,255,6]
    apply (native_lookup_binary .or #v[128,255,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨33023, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,255,255,7]
    apply (native_lookup_binary .and #v[255,255,255]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨65535, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,7,7,7]
    apply (native_lookup_binary .and #v[255,7,7]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨65287, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,7]
    apply (native_lookup_binary .and #v[0,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨0, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,0,0,7]
    apply (native_lookup_binary .and #v[128,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨32768, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[3,3,0,47]
    apply (native_lookup_scalar .truncate #v[3,3,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨3, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[262143,65528,7,48]
    apply (native_lookup_sll_low #v[262143,65528,7]).mpr
    apply (native_sll_low_membership _).mp
    exact ⟨⟨262143, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[229376,0,0,49]
    apply (native_lookup_sll_high #v[229376,0,0]).mpr
    apply (native_sll_high_membership _).mp
    exact ⟨⟨229376, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0]
    exact (native_lookup_zero #v[0,0,0]).mpr rfl
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[3,3,0,47]
    apply (native_lookup_scalar .truncate #v[3,3,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨3, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[262143,8191,0,50]
    apply (native_lookup_srl_low #v[262143,8191,0]).mpr
    apply (native_srl_low_membership _).mp
    exact ⟨⟨262143, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[229376,0,4096,51]
    apply (native_lookup_srl_high #v[229376,0,4096]).mpr
    apply (native_srl_high_membership _).mp
    exact ⟨⟨229376, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0]
    exact (native_lookup_zero #v[0,0,0]).mpr rfl
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[3,3,0,47]
    apply (native_lookup_scalar .truncate #v[3,3,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨3, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[229376,0,57344,52]
    apply (native_lookup_scalar .signFill #v[229376,0,57344]).mpr
    apply (native_shift_scalar_membership .signFill _).mp
    exact ⟨⟨229376, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[262143,8191,0,50]
    apply (native_lookup_srl_low #v[262143,8191,0]).mpr
    apply (native_srl_low_membership _).mp
    exact ⟨⟨262143, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[229376,0,4096,51]
    apply (native_lookup_srl_high #v[229376,0,4096]).mpr
    apply (native_srl_high_membership _).mp
    exact ⟨⟨229376, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,3,252,4]
    apply (native_lookup_binary .xor #v[255,3,252]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨65283, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,0,255,4]
    apply (native_lookup_binary .xor #v[255,0,255]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨65280, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,4]
    apply (native_lookup_binary .xor #v[0,0,0]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨0, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,0,128,4]
    apply (native_lookup_binary .xor #v[128,0,128]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨32768, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,3,255,6]
    apply (native_lookup_binary .or #v[255,3,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨65283, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,0,255,6]
    apply (native_lookup_binary .or #v[255,0,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨65280, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,6]
    apply (native_lookup_binary .or #v[0,0,0]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨0, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,0,128,6]
    apply (native_lookup_binary .or #v[128,0,128]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨32768, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,3,3,7]
    apply (native_lookup_binary .and #v[255,3,3]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨65283, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,0,0,7]
    apply (native_lookup_binary .and #v[255,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨65280, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,7]
    apply (native_lookup_binary .and #v[0,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨0, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,0,0,7]
    apply (native_lookup_binary .and #v[128,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨32768, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[31,31,0,47]
    apply (native_lookup_scalar .truncate #v[31,31,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨31, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2097151,0,32768,48]
    apply (native_lookup_sll_low #v[2097151,0,32768]).mpr
    apply (native_sll_low_membership _).mp
    exact ⟨⟨2097151, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2064384,0,0,49]
    apply (native_lookup_sll_high #v[2064384,0,0]).mpr
    apply (native_sll_high_membership _).mp
    exact ⟨⟨2064384, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0]
    exact (native_lookup_zero #v[0,0,0]).mpr rfl
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[31,31,0,47]
    apply (native_lookup_scalar .truncate #v[31,31,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨31, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2097151,0,0,50]
    apply (native_lookup_srl_low #v[2097151,0,0]).mpr
    apply (native_srl_low_membership _).mp
    exact ⟨⟨2097151, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2064384,1,0,51]
    apply (native_lookup_srl_high #v[2064384,1,0]).mpr
    apply (native_srl_high_membership _).mp
    exact ⟨⟨2064384, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0]
    exact (native_lookup_zero #v[0,0,0]).mpr rfl
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[1055,31,0,47]
    apply (native_lookup_scalar .truncate #v[1055,31,0]).mpr
    apply (native_shift_scalar_membership .truncate _).mp
    exact ⟨⟨1055, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2064384,65534,65535,52]
    apply (native_lookup_scalar .signFill #v[2064384,65534,65535]).mpr
    apply (native_shift_scalar_membership .signFill _).mp
    exact ⟨⟨2064384, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2097151,0,0,50]
    apply (native_lookup_srl_low #v[2097151,0,0]).mpr
    apply (native_srl_low_membership _).mp
    exact ⟨⟨2097151, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[2064384,1,0,51]
    apply (native_lookup_srl_high #v[2064384,1,0]).mpr
    apply (native_srl_high_membership _).mp
    exact ⟨⟨2064384, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,255,0,4]
    apply (native_lookup_binary .xor #v[255,255,0]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨65535, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,255,0,4]
    apply (native_lookup_binary .xor #v[255,255,0]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨65535, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,255,255,4]
    apply (native_lookup_binary .xor #v[0,255,255]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨255, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,255,127,4]
    apply (native_lookup_binary .xor #v[128,255,127]).mpr
    apply (native_binary_membership .xor _).mp
    exact ⟨⟨33023, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,0,255,6]
    apply (native_lookup_binary .or #v[255,0,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨65280, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,248,255,6]
    apply (native_lookup_binary .or #v[255,248,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨65528, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,255,255,6]
    apply (native_lookup_binary .or #v[0,255,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨255, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,255,255,6]
    apply (native_lookup_binary .or #v[128,255,255]).mpr
    apply (native_binary_membership .or _).mp
    exact ⟨⟨33023, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,255,255,7]
    apply (native_lookup_binary .and #v[255,255,255]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨65535, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[255,7,7,7]
    apply (native_lookup_binary .and #v[255,7,7]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨65287, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,7]
    apply (native_lookup_binary .and #v[0,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨0, by decide⟩, by decide +kernel⟩
  · change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[128,0,0,7]
    apply (native_lookup_binary .and #v[128,0,0]).mpr
    apply (native_binary_membership .and _).mp
    exact ⟨⟨32768, by decide⟩, by decide +kernel⟩

/-- Keep native query objects symbolic when assembling complete fixture acceptance. -/
theorem lookup_holds (sample : Fin 24) (slot : Fin 4) :
    (NativeShiftLookup.lookup
      #v[Expression.var ⟨39 + 4 * slot.val⟩, Expression.var ⟨40 + 4 * slot.val⟩,
         Expression.var ⟨41 + 4 * slot.val⟩]
      (Expression.var ⟨42 + 4 * slot.val⟩)).Contains
        (environment (assignment sample)) := by
  apply tagged_query_contains
  simpa only [Expression.eval, environment] using lookup_members sample slot

end Tests.ShiftRoutingQueries
