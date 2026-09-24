pub const MOP_ADD_MOD: u32 = 0;
pub const MOP_SUB_MOD: u32 = 1;
pub const MOP_MUL_MOD: u32 = 2;
pub const MOP_FMA_MOD: u32 = 3;
pub const MOP_TRI_ADD: u32 = 4;

// MOP-I (`mop.r.N`, rs1 -> rd) numbers. Non-zero N is a rotation (or xor-rotate) amount.
pub const MOP_I_BYTE_SWAP: u32 = 0;
