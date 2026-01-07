use super::*;

// NOTE: implementations below should match what replayer would do. Also these functions are called at the state
// which would be consistent with invoking just 1 `csrrw x0, csr, x0` opcode:
// - state.timestamp is 0 mod 4
// - x0 timestamp is state.timestamp + 2
// - state.timestamp += 3
// - memory is not yet touched

// On exit if multicycle sequences it should again be
// - x0 timestamp is 2 mod 4
// - ABI register timestamps are 3 mod 4
// - state.timestamp is 3 mod 4

mod bigint;
mod blake;
mod keccak;

pub use self::bigint::*;
pub use self::blake::*;
pub use self::keccak::*;
