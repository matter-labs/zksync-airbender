pub const REGISTER_SIZE: usize = 2;
pub const NUM_TIMESTAMP_COLUMNS_FOR_RAM: usize = 2;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ColumnSet<const WIDTH: usize> {
    pub start: u32,
    pub num_elements: u32,
}

impl<const WIDTH: usize> From<cs::definitions::ColumnSet<WIDTH>> for ColumnSet<WIDTH> {
    fn from(value: cs::definitions::ColumnSet<WIDTH>) -> Self {
        Self {
            start: value.start as u32,
            num_elements: value.num_elements as u32,
        }
    }
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub enum ColumnAddress {
    WitnessSubtree(u32),
    MemorySubtree(u32),
    SetupSubtree(u32),
    OptimizedOut(u32),
}

impl Default for ColumnAddress {
    fn default() -> Self {
        Self::WitnessSubtree(0)
    }
}

impl From<cs::definitions::ColumnAddress> for ColumnAddress {
    fn from(value: cs::definitions::ColumnAddress) -> Self {
        match value {
            cs::definitions::ColumnAddress::WitnessSubtree(x) => Self::WitnessSubtree(x as u32),
            cs::definitions::ColumnAddress::MemorySubtree(x) => Self::MemorySubtree(x as u32),
            cs::definitions::ColumnAddress::SetupSubtree(x) => Self::SetupSubtree(x as u32),
            cs::definitions::ColumnAddress::OptimizedOut(x) => Self::OptimizedOut(x as u32),
        }
    }
}
