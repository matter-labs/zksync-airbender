use super::column::ColumnAddress;
use super::layout::ShuffleRamInitAndTeardownLayout;
use super::ram_access::{ShuffleRamAuxComparisonSet, ShuffleRamQueryColumns};
use std::ops::Deref;

pub const MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct MemoryQueriesTimestampComparisonAuxVars {
    count: u32,
    addresses: [ColumnAddress; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
}

impl<T: Deref<Target = [cs::definitions::ColumnAddress]>> From<&T>
    for MemoryQueriesTimestampComparisonAuxVars
{
    fn from(value: &T) -> Self {
        let value = value.as_ref();
        let len = value.len();
        assert!(len <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT);
        let count = len as u32;
        let mut addresses = [ColumnAddress::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
        for (&src, dst) in value.iter().zip(addresses.iter_mut()) {
            *dst = src.into();
        }
        Self { count, addresses }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamAccessSets {
    pub count: u32,
    pub sets: [ShuffleRamQueryColumns; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
}

impl<T: Deref<Target = [cs::definitions::ShuffleRamQueryColumns]>> From<&T>
    for ShuffleRamAccessSets
{
    fn from(value: &T) -> Self {
        let len = value.len();
        assert!(len <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT);
        let count = len as u32;
        let mut sets = [ShuffleRamQueryColumns::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
        for (&src, dst) in value.iter().zip(sets.iter_mut()) {
            *dst = src.into();
        }
        Self { count, sets }
    }
}

pub const MAX_INITS_AND_TEARDOWNS_SETS_COUNT: usize = 16;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamAuxComparisonSets {
    pub count: u32,
    pub sets: [ShuffleRamAuxComparisonSet; MAX_INITS_AND_TEARDOWNS_SETS_COUNT],
}

impl<T: Deref<Target = [cs::definitions::ShuffleRamAuxComparisonSet]>> From<&T>
    for ShuffleRamAuxComparisonSets
{
    fn from(value: &T) -> Self {
        let len = value.len();
        assert!(len <= MAX_INITS_AND_TEARDOWNS_SETS_COUNT);
        let count = len as u32;
        let mut sets = [ShuffleRamAuxComparisonSet::default(); MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
        for (&src, dst) in value.iter().zip(sets.iter_mut()) {
            *dst = src.into();
        }
        Self { count, sets }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamInitAndTeardownLayouts {
    pub count: u32,
    pub layouts: [ShuffleRamInitAndTeardownLayout; MAX_INITS_AND_TEARDOWNS_SETS_COUNT],
}

impl<T: Deref<Target = [cs::definitions::ShuffleRamInitAndTeardownLayout]>> From<&T>
    for ShuffleRamInitAndTeardownLayouts
{
    fn from(value: &T) -> Self {
        let len = value.len();
        assert!(len <= MAX_INITS_AND_TEARDOWNS_SETS_COUNT);
        let count = len as u32;
        let mut layouts =
            [ShuffleRamInitAndTeardownLayout::default(); MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
        for (&src, dst) in value.iter().zip(layouts.iter_mut()) {
            *dst = src.into();
        }
        Self { count, layouts }
    }
}
