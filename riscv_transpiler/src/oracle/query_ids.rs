//! The query IDs that the oracle side itself interprets. A guest starts every query with an ID;
//! the IDs of the queries of a program are allocated by the program's platform, in subspaces by
//! bitmask, and only the system queries below are known to the dispatcher.

/// Second bit, the basic queries
pub const BASIC_SUBSPACE_MASK: u32 = 0x40_00_00_00;

/// System queries
#[allow(clippy::identity_op)]
pub const SYSTEM_SUBSPACE_MASK: u32 = BASIC_SUBSPACE_MASK | 0x00_00_00_00; // 0x40000000

/// UART output, for debugging: the start of a QuasiUART frame, not a query
pub const UART_QUERY_ID: u32 = crate::abstractions::non_determinism::UartFrame::HELLO_VALUE;

/// Disconnects the guest from the external oracle: execution continues on its own
#[allow(clippy::identity_op)]
pub const DISCONNECT_ORACLE_QUERY_ID: u32 = SYSTEM_SUBSPACE_MASK | 0; // 0x40000000

/// The zero-knowledge masking stream of the exit sequence (see [`super::zk_masking`]). The value
/// is a parameter of the guest's assembly sequence, so it is defined next to it.
pub const ZK_MASKING_QUERY_ID: u32 = riscv_common::zk_masking::MASKING_QUERY_ID; // 0x40000001

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_ids_are_the_wire_protocol() {
        assert_eq!(SYSTEM_SUBSPACE_MASK, 0x4000_0000);
        assert_eq!(DISCONNECT_ORACLE_QUERY_ID, 0x4000_0000);
        assert_eq!(ZK_MASKING_QUERY_ID, 0x4000_0001);
        assert_eq!(UART_QUERY_ID, u32::MAX);
    }
}
