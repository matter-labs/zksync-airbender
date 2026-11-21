//! The oracle side of the memory-based query protocol of guests, on the host.
//!
//! For the guest the oracle is the non-determinism CSR, a channel of words. A query is exactly
//! two words written to it, the query ID (see [`query_ids`]) and one *input word*: `0` for a
//! query without input, a short value itself, or the address of the input (e.g. a request
//! struct) in the memory of the querier, which the oracle reads while it receives the word. The
//! response is exactly the words the querier then reads, without a length prefix.
//!
//! - [`OracleQueryProcessor`] is a responder to queries, by query ID, and [`RunMode`] the run
//!   it responds for. It reads the inputs of a query through [`QuerierMemory`]
//!   ([`GuestMemory`] for the RISC-V guest, [`NativeQuerierMemory`] for a querier in this
//!   process).
//! - [`QueryDispatcher`] dispatches queries to the processors, and is the non-determinism CSR
//!   source of the simulators (transpiler-based and JIT). It also serves a querier in this
//!   process, and [`ReadWitnessSource`] records what the guest reads.
//! - [`GuestSource`] is the CSR source of a guest that first reads plain input words and then
//!   sends queries.
//! - [`zk_masking`] has the responder of the zero-knowledge masking query, which the exit
//!   sequence `riscv_common::finish_execution_recursion_extended` sends.
//!
//! The querier side (the trait a querier is written against, its error type, the encodings of
//! values, and the registry of the query IDs of programs) stays with the queriers' crates.
//!
//! # Security
//!
//! Everything the oracle sends is untrusted: the querier validates the encoding of a response,
//! and checks that the value is correct, before it uses it.

mod dispatcher;
mod guest_source;
mod querier_memory;
pub mod query_ids;
mod query_processor;
pub mod zk_masking;

pub use self::dispatcher::{query_timing, QueryDispatcher, QueryError, ReadWitnessSource};
pub use self::guest_source::GuestSource;
pub use self::querier_memory::{
    offset_address, read_querier_u32_words_into, read_querier_word, GuestMemory,
    NativeQuerierMemory, QuerierMemory, QuerierMemoryError,
};
pub use self::query_processor::{respond_to_every_target, OracleQueryProcessor, RunMode};
