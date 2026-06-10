#include "gkr_forward_generation.cuh"

// The forward code-generation challenge values that used to live in
// `__constant__` tables here (ab_gkr_perm_challenges / ab_gkr_perm_additive /
// ab_gkr_decoder_fill_value) now ride in the kernel proxy (`GkrFwdProxy`): the
// permutation challenges + additive seed by value (host-known at schedule
// time), the decoder fill value by pointer (device-computed in setup). This
// removes the per-launch H2D uploads and the D2D copy the A/B path previously
// scheduled. The shared `ab_gkr_lookup_gamma_consts` / `ab_gkr_lookup_alpha_powers`
// tables are still owned by flat_layer.cu / setup/kernels.cu. No definitions
// remain in this translation unit.
