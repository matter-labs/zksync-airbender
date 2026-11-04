use crate::definitions::LazyInitAndTeardown;
use cs::definitions::TimestampScalar;
use fft::GoodAllocator;
use std::alloc::Global;

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
#[serde(bound = "Vec<LazyInitAndTeardown, A>: serde::Serialize + serde::de::DeserializeOwned")]
pub struct ShuffleRamSetupAndTeardown<A: GoodAllocator = Global> {
    pub lazy_init_data: Vec<LazyInitAndTeardown, A>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RamShuffleMemStateRecord {
    pub last_access_timestamp: TimestampScalar,
    pub current_value: u32,
}
