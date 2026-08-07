//! Offline forward schedule search: DAG-native genome structure, a traffic
//! floor, and a compile-in-loop objective. Candidates are scored by the real
//! compiler rather than a replay model.

mod floor;
mod genome;
pub(crate) mod producer;
mod scorer;
mod search;
