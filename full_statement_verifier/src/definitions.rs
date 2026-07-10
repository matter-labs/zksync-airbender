pub const OP_VERIFY_UNROLLED_RECURSION_LAYER_IN_UNIFIED_CIRCUIT: u32 = 1;
pub const OP_VERIFY_UNIFIED_RECURSION_LAYER_IN_UNIFIED_CIRCUIT: u32 = 2;
/// Combine multiple proofs (from recursion layers) into one.
/// Requires u32 to be passed as the next word after this one,
/// indicating how many proofs are combined. Each combined proof stream
/// then starts with its own op word (one of the two ops above).
// Used to combine multiple batch FRI proofs into a single proof before SNARKing.
pub const OP_VERIFY_COMBINED_RECURSION_LAYERS_IN_UNIFIED_CIRCUIT: u32 = 3;

pub const OP_VERIFY_BASE_LAYER_IN_UNROLLED_CIRCUITS: u32 = 1;
pub const OP_VERIFY_RECURSIVE_LAYER_IN_UNROLLED_CIRCUITS: u32 = 2;
