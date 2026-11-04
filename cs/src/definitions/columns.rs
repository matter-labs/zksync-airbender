use super::*;

#[derive(Clone, Copy, Hash, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct ColumnSet<const WIDTH: usize> {
    pub start: usize,
    pub num_elements: usize,
}

impl<const WIDTH: usize> ColumnSet<WIDTH> {
    pub const fn empty() -> Self {
        Self {
            start: 0,
            num_elements: 0,
        }
    }

    pub const fn new(start: usize, num_elements: usize) -> Self {
        Self {
            start,
            num_elements,
        }
    }

    pub fn layout_at(offset: &mut usize, num_elements: usize) -> Self {
        assert!(WIDTH > 0);

        let start = *offset;
        *offset += num_elements * WIDTH;

        Self {
            start,
            num_elements,
        }
    }

    pub const fn width(&self) -> usize {
        WIDTH
    }

    pub const fn start(&self) -> usize {
        self.start
    }

    pub const fn num_elements(&self) -> usize {
        self.num_elements
    }

    pub const fn full_range(&self) -> Range<usize> {
        self.start..(self.start + WIDTH * self.num_elements)
    }

    pub fn iter(&self) -> impl Iterator<Item = Range<usize>> {
        let mut offset = self.start;
        core::iter::repeat_with(move || {
            let range = offset..(offset + WIDTH);
            offset += WIDTH;

            range
        })
        .take(self.num_elements)
    }

    #[track_caller]
    pub fn get_range(&self, idx: usize) -> Range<usize> {
        assert!(idx < self.num_elements);

        let start = self.start + (WIDTH * idx);
        let end = start + WIDTH;

        start..end
    }
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct AlignedColumnSet<const WIDTH: usize> {
    pub start: usize,
    pub num_elements: usize,
}

impl<const WIDTH: usize> AlignedColumnSet<WIDTH> {
    pub const fn empty() -> Self {
        Self {
            start: 0,
            num_elements: 0,
        }
    }

    pub const fn new(start: usize, num_elements: usize) -> Self {
        Self {
            start,
            num_elements,
        }
    }

    pub fn layout_at(offset: &mut usize, num_elements: usize) -> Self {
        assert!(WIDTH > 0);
        assert!(WIDTH.is_power_of_two());

        if *offset % WIDTH != 0 {
            *offset = offset.next_multiple_of(WIDTH);
        }

        let start = *offset;
        *offset += num_elements * WIDTH;

        Self {
            start,
            num_elements,
        }
    }

    pub const fn width(&self) -> usize {
        WIDTH
    }

    pub const fn start(&self) -> usize {
        self.start
    }

    pub const fn num_elements(&self) -> usize {
        self.num_elements
    }

    pub const fn full_range(&self) -> Range<usize> {
        self.start..(self.start + WIDTH * self.num_elements)
    }

    pub fn iter(&self) -> impl Iterator<Item = Range<usize>> {
        let mut offset = self.start;
        core::iter::repeat_with(move || {
            let range = offset..(offset + WIDTH);
            offset += WIDTH;

            range
        })
        .take(self.num_elements)
    }

    #[track_caller]
    pub const fn get_range(&self, idx: usize) -> Range<usize> {
        debug_assert!(idx < self.num_elements);

        let start = self.start + (WIDTH * idx);
        let end = start + WIDTH;

        start..end
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum ColumnAddress {
    WitnessSubtree(usize),
    MemorySubtree(usize),
    SetupSubtree(usize),
    OptimizedOut(usize),
}

impl ColumnAddress {
    pub const fn placeholder() -> Self {
        Self::OptimizedOut(0)
    }

    #[inline(always)]
    pub const fn offset(&self) -> usize {
        match self {
            Self::WitnessSubtree(offset) => *offset,
            Self::MemorySubtree(offset) => *offset,
            Self::SetupSubtree(offset) => *offset,
            Self::OptimizedOut(offset) => *offset,
        }
    }
}
