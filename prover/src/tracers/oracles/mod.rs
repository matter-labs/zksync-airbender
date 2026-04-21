// NOTE: These oracles are not guaranteed to be used at all for CPU provers,
// but implementations are given for ease of porting of the same functionality on GPU

use cs::definitions::{TimestampData, TimestampScalar};
use fft::GoodAllocator;
use worker::Worker;

pub mod transpiler_oracles;
