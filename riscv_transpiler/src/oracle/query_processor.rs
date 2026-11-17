//! The responders of the oracle side: what a crate implements to answer its queries.
//! [`OracleQueryProcessor`] is a responder, and [`RunMode`] the run it responds for.

use super::querier_memory::QuerierMemory;

/// The run an oracle serves: where the queries come from, and which responses its processors
/// produce (see [`OracleQueryProcessor::process_memory_query`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RunMode {
    /// A native run: the queries come from a querier in this process, and are answered for it
    /// only.
    #[default]
    NativeRunOnly,
    /// A native run that records the prover input: the queries come from a querier in this
    /// process, and are also answered for the RISC-V guest, whose responses are saved for its
    /// replay (see [`ReadWitnessSource`](super::ReadWitnessSource)).
    NativeRunSavingForRiscV,
    /// A run of the RISC-V guest in the simulator: the queries, and the memory pointers in them,
    /// come from the guest, and are answered for it only.
    RiscVRun,
}

impl RunMode {
    /// Whether the queries come from a querier in this process, which the responses of the
    /// native run are produced for
    pub const fn produces_native_run_responses(self) -> bool {
        match self {
            Self::NativeRunOnly | Self::NativeRunSavingForRiscV => true,
            Self::RiscVRun => false,
        }
    }

    /// Whether the responses of the RISC-V guest run are produced: to serve the guest, or to
    /// save them for its replay
    pub const fn produces_guest_run_responses(self) -> bool {
        match self {
            Self::NativeRunOnly => false,
            Self::NativeRunSavingForRiscV | Self::RiscVRun => true,
        }
    }
}

/// A responder to memory-based queries, by query ID.
pub trait OracleQueryProcessor {
    /// IDs of the queries served (see the [module documentation](super)).
    fn supported_memory_query_ids(&self) -> Vec<u32>;

    /// Serves a query. `input_word` is the input word the querier sent, and `memory` reads the
    /// memory of the querier it may refer to. `mode` tells the querier apart: a querier in this
    /// process (a native run), or the RISC-V guest in the simulator, which the memory pointers of
    /// the query then belong to.
    ///
    /// Appends the response words, exactly as the querier reads them, for the runs of `mode`: to
    /// `native_run_responses` as a querier in this process reads them, to `guest_run_responses`
    /// as the RISC-V guest reads them. The oracle serves the responses of its querier, and a
    /// native run that records the prover input saves the responses of the guest run, which the
    /// guest reads in place of the native querier on replay (see
    /// [`ReadWitnessSource`](super::ReadWitnessSource)); a run on
    /// the RISC-V guest has no responses of a native run. A response that is the same on every
    /// target goes through [`respond_to_every_target`]; the field hints, for example, follow the
    /// representation of field elements on each target.
    fn process_memory_query(
        &mut self,
        query_id: u32,
        input_word: usize,
        memory: &dyn QuerierMemory,
        mode: RunMode,
        native_run_responses: &mut Vec<u32>,
        guest_run_responses: &mut Vec<u32>,
    );
}

/// Appends a response that is the same on every target to the responses of the runs of `mode`
/// (see [`OracleQueryProcessor::process_memory_query`]).
pub fn respond_to_every_target(
    mode: RunMode,
    mut response: Vec<u32>,
    native_run_responses: &mut Vec<u32>,
    guest_run_responses: &mut Vec<u32>,
) {
    match mode {
        RunMode::NativeRunOnly => native_run_responses.append(&mut response),
        RunMode::NativeRunSavingForRiscV => {
            guest_run_responses.extend_from_slice(&response);
            native_run_responses.append(&mut response);
        }
        RunMode::RiscVRun => guest_run_responses.append(&mut response),
    }
}
