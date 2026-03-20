use itertools::Itertools;
use std::alloc::AllocError;
use std::collections::{BTreeMap, BTreeSet, Bound};
use std::ptr::NonNull;

type Addr = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocationPlacement {
    BestFit,
    Bottom,
    Top,
}

pub struct AllocationsTracker {
    ptrs: Vec<Addr>,
    lens: Vec<usize>,
    free_len_by_addr: BTreeMap<Addr, usize>,
    free_addrs_by_len: BTreeMap<usize, BTreeSet<Addr>>,
    used_mem_current: usize,
    used_mem_peak: usize,
}

impl AllocationsTracker {
    pub fn new(ptrs_and_lens: &[(NonNull<u8>, usize)]) -> Self {
        let addrs_and_lens = ptrs_and_lens
            .iter()
            .map(|&(ptr, len)| (Self::addr_from_ptr(ptr), len))
            .collect_vec();
        Self::new_from_addrs(&addrs_and_lens)
    }

    #[cfg(test)]
    fn from_raw_regions(addrs_and_lens: &[(usize, usize)]) -> Self {
        Self::new_from_addrs(addrs_and_lens)
    }

    fn new_from_addrs(addrs_and_lens: &[(Addr, usize)]) -> Self {
        assert!(
            !addrs_and_lens.is_empty(),
            "allocation tracker requires at least one region"
        );
        let len = addrs_and_lens.len();
        let mut ptrs = Vec::with_capacity(len);
        let mut lens = Vec::with_capacity(len);
        let mut free_len_by_addr = BTreeMap::new();
        let mut free_addrs_by_len = BTreeMap::new();

        let mut last_end = None;
        for &(addr, len) in addrs_and_lens.iter().sorted() {
            assert_ne!(addr, 0, "allocation regions must be non-null");
            assert_ne!(len, 0, "allocation regions must be non-empty");
            let end = Self::end_addr(addr, len);
            if let Some(last_end) = last_end {
                assert!(last_end <= addr, "allocation regions must not overlap");
            }
            last_end = Some(end);

            ptrs.push(addr);
            lens.push(len);
            assert!(
                free_len_by_addr.insert(addr, len).is_none(),
                "duplicate region start address"
            );
            let addrs = free_addrs_by_len.entry(len).or_insert_with(BTreeSet::new);
            addrs.insert(addr);
        }

        let tracker = Self {
            ptrs,
            lens,
            free_len_by_addr,
            free_addrs_by_len,
            used_mem_current: 0,
            used_mem_peak: 0,
        };
        tracker.assert_invariants();
        tracker
    }

    pub fn capacity(&self) -> usize {
        self.lens.iter().sum()
    }

    fn addr_from_ptr(ptr: NonNull<u8>) -> Addr {
        ptr.as_ptr() as Addr
    }

    fn ptr_from_addr(addr: Addr) -> NonNull<u8> {
        NonNull::new(addr as *mut u8).expect("tracked allocation address must be non-null")
    }

    fn end_addr(addr: Addr, len: usize) -> Addr {
        addr.checked_add(len)
            .expect("tracked allocation address range overflowed")
    }

    fn region_end(&self, idx: usize) -> Addr {
        Self::end_addr(self.ptrs[idx], self.lens[idx])
    }

    fn region_index_for_addr(&self, addr: Addr) -> usize {
        match self.ptrs.binary_search(&addr) {
            Ok(idx) => idx,
            Err(0) => panic!("out of bounds free"),
            Err(idx) => idx - 1,
        }
    }

    fn range_fits_in_region(&self, idx: usize, addr: Addr, len: usize) -> bool {
        let end = Self::end_addr(addr, len);
        addr >= self.ptrs[idx] && end <= self.region_end(idx)
    }

    fn insert_free_block(&mut self, addr: Addr, len: usize) {
        let idx = self.region_index_for_addr(addr);
        assert!(
            self.range_fits_in_region(idx, addr, len),
            "free block must fit fully inside its region"
        );
        assert!(self.free_len_by_addr.insert(addr, len).is_none());
        assert!(self
            .free_addrs_by_len
            .entry(len)
            .or_default()
            .insert(addr));
    }

    fn remove_free_block(&mut self, addr: Addr, len: usize) {
        assert_eq!(self.free_len_by_addr.remove(&addr), Some(len));
        Self::remove_free_addr_from_len_bucket(&mut self.free_addrs_by_len, addr, len);
    }

    fn remove_free_addr_from_len_bucket(
        free_addrs_by_len: &mut BTreeMap<usize, BTreeSet<Addr>>,
        addr: Addr,
        len: usize,
    ) {
        let addrs = free_addrs_by_len
            .get_mut(&len)
            .expect("free length bucket must exist");
        assert!(addrs.remove(&addr));
        if addrs.is_empty() {
            assert!(free_addrs_by_len
                .remove(&len)
                .expect("free length bucket must still exist")
                .is_empty());
        }
    }

    fn insert_remainder(
        &mut self,
        free_addr: Addr,
        free_len: usize,
        len: usize,
        placement: AllocationPlacement,
    ) -> Addr {
        assert!(free_len > len);
        let remainder_len = free_len - len;
        let (addr, remainder_addr) = match placement {
            AllocationPlacement::Top => (Self::end_addr(free_addr, remainder_len), free_addr),
            _ => (free_addr, Self::end_addr(free_addr, len)),
        };
        self.insert_free_block(remainder_addr, remainder_len);
        addr
    }

    fn alloc_best_fit(&mut self, len: usize) -> Result<Addr, AllocError> {
        let mut cursor = self.free_addrs_by_len.lower_bound_mut(Bound::Included(&len));
        if let Some((&free_len, free_addrs)) = cursor.peek_next() {
            let free_addr = free_addrs.pop_first().unwrap();
            if free_addrs.is_empty() {
                cursor.remove_next();
            }
            assert_eq!(self.free_len_by_addr.remove(&free_addr), Some(free_len));
            Ok(if free_len == len {
                free_addr
            } else {
                self.insert_remainder(free_addr, free_len, len, AllocationPlacement::BestFit)
            })
        } else {
            Err(AllocError)
        }
    }

    fn find_free_addr_by_len<'a>(
        mut iter: impl Iterator<Item = (&'a Addr, &'a usize)>,
        len: usize,
    ) -> Option<Addr> {
        iter.find_map(|(&addr, &l)| if l >= len { Some(addr) } else { None })
    }

    fn alloc_at_free_addr(
        &mut self,
        free_addr: Option<Addr>,
        len: usize,
        placement: AllocationPlacement,
    ) -> Result<Addr, AllocError> {
        if let Some(free_addr) = free_addr {
            let free_len = self
                .free_len_by_addr
                .get(&free_addr)
                .copied()
                .expect("free block must exist");
            self.remove_free_block(free_addr, free_len);
            assert!(free_len >= len);
            Ok(if free_len == len {
                free_addr
            } else {
                self.insert_remainder(free_addr, free_len, len, placement)
            })
        } else {
            Err(AllocError)
        }
    }

    fn alloc_bottom(&mut self, len: usize) -> Result<Addr, AllocError> {
        let free_addr = Self::find_free_addr_by_len(self.free_len_by_addr.iter(), len);
        self.alloc_at_free_addr(free_addr, len, AllocationPlacement::Bottom)
    }

    fn alloc_top(&mut self, len: usize) -> Result<Addr, AllocError> {
        let free_addr = Self::find_free_addr_by_len(self.free_len_by_addr.iter().rev(), len);
        self.alloc_at_free_addr(free_addr, len, AllocationPlacement::Top)
    }

    pub fn alloc(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> Result<NonNull<u8>, AllocError> {
        if len == 0 {
            return Ok(Self::ptr_from_addr(self.ptrs[0]));
        }
        let result = match placement {
            AllocationPlacement::BestFit => self.alloc_best_fit(len),
            AllocationPlacement::Bottom => self.alloc_bottom(len),
            AllocationPlacement::Top => self.alloc_top(len),
        };
        if result.is_ok() {
            self.used_mem_current += len;
            self.used_mem_peak = self.used_mem_peak.max(self.used_mem_current);
            self.assert_invariants();
        }
        result.map(Self::ptr_from_addr)
    }

    pub fn free(&mut self, mut ptr: NonNull<u8>, mut len: usize) {
        if len == 0 {
            assert_eq!(ptr, Self::ptr_from_addr(self.ptrs[0]));
            return;
        }

        self.used_mem_current = self
            .used_mem_current
            .checked_sub(len)
            .expect("allocator usage underflow during free");

        let mut addr = Self::addr_from_ptr(ptr);
        let region_idx = self.region_index_for_addr(addr);
        let region_start = self.ptrs[region_idx];
        let region_end = self.region_end(region_idx);
        assert!(
            self.range_fits_in_region(region_idx, addr, len),
            "out of bounds free"
        );

        let (free_len_by_addr, free_addrs_by_len) =
            (&mut self.free_len_by_addr, &mut self.free_addrs_by_len);
        let mut cursor = free_len_by_addr.lower_bound_mut(Bound::Included(&addr));
        if let Some((&next_addr, &mut next_len)) = cursor.peek_next() {
            if next_addr < region_end {
                let end = Self::end_addr(addr, len);
                assert!(next_addr >= end, "double free");
                if next_addr == end {
                    cursor.remove_next();
                    Self::remove_free_addr_from_len_bucket(free_addrs_by_len, next_addr, next_len);
                    len += next_len;
                }
            }
        }
        if let Some((&prev_addr, &mut prev_len)) = cursor.peek_prev() {
            if prev_addr >= region_start {
                let prev_end = Self::end_addr(prev_addr, prev_len);
                assert!(addr >= prev_end, "double free");
                if addr == prev_end {
                    cursor.remove_prev();
                    Self::remove_free_addr_from_len_bucket(free_addrs_by_len, prev_addr, prev_len);
                    addr = prev_addr;
                    ptr = Self::ptr_from_addr(addr);
                    len += prev_len;
                }
            }
        }

        assert_eq!(Self::addr_from_ptr(ptr), addr);
        self.insert_free_block(addr, len);
        self.assert_invariants();
    }

    pub fn get_used_mem_current(&self) -> usize {
        self.used_mem_current
    }

    pub fn get_used_mem_peak(&self) -> usize {
        self.used_mem_peak
    }

    pub fn reset_used_mem_peak(&mut self) {
        self.used_mem_peak = self.used_mem_current;
    }

    #[cfg(debug_assertions)]
    fn assert_invariants(&self) {
        debug_assert!(self.used_mem_current <= self.capacity());

        let mut free_mem_total = 0usize;
        let mut prev: Option<(Addr, usize, usize)> = None;
        for (&addr, &len) in self.free_len_by_addr.iter() {
            let idx = self.region_index_for_addr(addr);
            debug_assert!(
                self.range_fits_in_region(idx, addr, len),
                "free block must stay within a single region"
            );
            debug_assert!(self
                .free_addrs_by_len
                .get(&len)
                .is_some_and(|addrs| addrs.contains(&addr)));
            if let Some((prev_addr, prev_len, prev_idx)) = prev {
                let prev_end = Self::end_addr(prev_addr, prev_len);
                debug_assert!(
                    prev_end <= addr,
                    "free blocks must be globally non-overlapping"
                );
                if prev_idx == idx {
                    debug_assert!(
                        prev_end < addr,
                        "adjacent free blocks in the same region must be coalesced"
                    );
                }
            }
            free_mem_total += len;
            prev = Some((addr, len, idx));
        }

        for (&len, addrs) in self.free_addrs_by_len.iter() {
            for &addr in addrs.iter() {
                debug_assert_eq!(self.free_len_by_addr.get(&addr), Some(&len));
            }
        }

        debug_assert_eq!(
            free_mem_total + self.used_mem_current,
            self.capacity(),
            "free and used memory must partition the tracked regions"
        );
    }

    #[cfg(not(debug_assertions))]
    fn assert_invariants(&self) {}
}

unsafe impl Send for AllocationsTracker {}

#[cfg(test)]
mod tests {
    use super::{AllocationPlacement, AllocationsTracker};

    const REGION_A: usize = 0x1000;
    const REGION_B: usize = 0x2000;
    const REGION_ADJACENT_B: usize = 0x1100;
    const REGION_LEN: usize = 0x100;

    fn tracker(regions: &[(usize, usize)]) -> AllocationsTracker {
        AllocationsTracker::from_raw_regions(regions)
    }

    fn assert_free_blocks(tracker: &AllocationsTracker, expected: &[(usize, usize)]) {
        let actual = tracker
            .free_len_by_addr
            .iter()
            .map(|(&addr, &len)| (addr, len))
            .collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn single_region_alloc_free_merge_for_all_placements() {
        let mut tracker = tracker(&[(REGION_A, REGION_LEN)]);

        let bottom = tracker.alloc(0x20, AllocationPlacement::Bottom).unwrap();
        let top = tracker.alloc(0x20, AllocationPlacement::Top).unwrap();
        let best_fit = tracker.alloc(0x20, AllocationPlacement::BestFit).unwrap();

        assert_eq!(bottom.as_ptr() as usize, REGION_A);
        assert_eq!(best_fit.as_ptr() as usize, REGION_A + 0x20);
        assert_eq!(top.as_ptr() as usize, REGION_A + 0xE0);
        assert_eq!(tracker.get_used_mem_current(), 0x60);
        assert_eq!(tracker.get_used_mem_peak(), 0x60);
        assert_free_blocks(&tracker, &[(REGION_A + 0x40, 0xA0)]);

        tracker.free(best_fit, 0x20);
        tracker.free(top, 0x20);
        tracker.free(bottom, 0x20);

        assert_eq!(tracker.get_used_mem_current(), 0);
        assert_eq!(tracker.get_used_mem_peak(), 0x60);
        assert_free_blocks(&tracker, &[(REGION_A, REGION_LEN)]);
    }

    #[test]
    fn multi_region_free_does_not_merge_across_regions() {
        let mut tracker = tracker(&[(REGION_A, REGION_LEN), (REGION_B, REGION_LEN)]);

        let first = tracker.alloc(REGION_LEN, AllocationPlacement::Bottom).unwrap();
        let second = tracker.alloc(REGION_LEN, AllocationPlacement::Bottom).unwrap();

        assert_eq!(first.as_ptr() as usize, REGION_A);
        assert_eq!(second.as_ptr() as usize, REGION_B);
        assert_eq!(tracker.get_used_mem_current(), 2 * REGION_LEN);
        assert_eq!(tracker.get_used_mem_peak(), 2 * REGION_LEN);

        tracker.free(first, REGION_LEN);
        assert_free_blocks(&tracker, &[(REGION_A, REGION_LEN)]);

        tracker.free(second, REGION_LEN);
        assert_eq!(tracker.get_used_mem_current(), 0);
        assert_eq!(tracker.get_used_mem_peak(), 2 * REGION_LEN);
        assert_free_blocks(&tracker, &[(REGION_A, REGION_LEN), (REGION_B, REGION_LEN)]);
    }

    #[test]
    fn adjacent_regions_do_not_coalesce_even_when_addresses_touch() {
        let mut tracker = tracker(&[(REGION_A, REGION_LEN), (REGION_ADJACENT_B, REGION_LEN)]);

        let first = tracker.alloc(REGION_LEN, AllocationPlacement::Bottom).unwrap();
        let second = tracker.alloc(REGION_LEN, AllocationPlacement::Bottom).unwrap();

        tracker.free(first, REGION_LEN);
        tracker.free(second, REGION_LEN);

        assert_eq!(tracker.get_used_mem_current(), 0);
        assert_eq!(tracker.get_used_mem_peak(), 2 * REGION_LEN);
        assert_free_blocks(
            &tracker,
            &[(REGION_A, REGION_LEN), (REGION_ADJACENT_B, REGION_LEN)],
        );
    }

    #[test]
    fn usage_counters_stay_within_capacity_through_multi_region_sequence() {
        let mut tracker = tracker(&[(REGION_A, REGION_LEN), (REGION_B, REGION_LEN)]);
        let capacity = tracker.capacity();

        let a = tracker.alloc(0x80, AllocationPlacement::Bottom).unwrap();
        assert!(tracker.get_used_mem_current() <= capacity);
        assert!(tracker.get_used_mem_peak() <= capacity);

        let b = tracker.alloc(0x40, AllocationPlacement::Top).unwrap();
        assert!(tracker.get_used_mem_current() <= capacity);
        assert!(tracker.get_used_mem_peak() <= capacity);

        let c = tracker.alloc(0xC0, AllocationPlacement::BestFit).unwrap();
        assert!(tracker.get_used_mem_current() <= capacity);
        assert!(tracker.get_used_mem_peak() <= capacity);

        tracker.free(b, 0x40);
        tracker.free(a, 0x80);
        tracker.free(c, 0xC0);

        assert_eq!(tracker.get_used_mem_current(), 0);
        assert!(tracker.get_used_mem_peak() <= capacity);
        assert_free_blocks(&tracker, &[(REGION_A, REGION_LEN), (REGION_B, REGION_LEN)]);
    }
}
