//! Offline forward schedule search: DAG-native genome structure, a traffic
//! floor, and a compile-in-loop objective. Candidates are scored by the real
//! compiler rather than a replay model.

pub mod decode;
pub mod floor;
pub mod genome;
pub mod producer;
pub mod scorer;
pub mod search;
pub mod structure;
