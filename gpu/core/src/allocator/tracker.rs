use itertools::Itertools;
use std::alloc::AllocError;
use std::collections::{BTreeMap, BTreeSet, Bound};
use std::ops::Range;
use std::ptr::NonNull;

type Addr = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocationPlacement {
    BestFit,
    Bottom,
    Top,
}

/// `Descending` mirrors every placement: `Bottom` takes the highest fitting
/// address, `Top` the lowest, and `BestFit` breaks ties toward the highest
/// address and fills its hole from the top.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocationDirection {
    Ascending,
    Descending,
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

    pub fn span(&self) -> (Addr, usize) {
        let start = self.ptrs[0];
        (start, self.region_end(self.ptrs.len() - 1) - start)
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

    fn align_up(addr: Addr, alignment: usize) -> Addr {
        debug_assert!(alignment.is_power_of_two());
        Self::end_addr(addr, alignment - 1) & !(alignment - 1)
    }

    fn align_down(addr: Addr, alignment: usize) -> Addr {
        debug_assert!(alignment.is_power_of_two());
        addr & !(alignment - 1)
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
        assert!(self.free_addrs_by_len.entry(len).or_default().insert(addr));
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

    fn aligned_addr_in_free_block(
        free_addr: Addr,
        free_len: usize,
        len: usize,
        placement: AllocationPlacement,
        alignment: usize,
    ) -> Option<Addr> {
        let free_end = Self::end_addr(free_addr, free_len);
        match placement {
            AllocationPlacement::Top => {
                let latest_start = free_end.checked_sub(len)?;
                let aligned_addr = Self::align_down(latest_start, alignment);
                (aligned_addr >= free_addr).then_some(aligned_addr)
            }
            AllocationPlacement::BestFit | AllocationPlacement::Bottom => {
                let aligned_addr = Self::align_up(free_addr, alignment);
                (Self::end_addr(aligned_addr, len) <= free_end).then_some(aligned_addr)
            }
        }
    }

    fn take_allocation_from_free_block(
        &mut self,
        free_addr: Addr,
        free_len: usize,
        alloc_addr: Addr,
        len: usize,
    ) -> Addr {
        self.remove_free_block(free_addr, free_len);

        let prefix_len = alloc_addr - free_addr;
        if prefix_len > 0 {
            self.insert_free_block(free_addr, prefix_len);
        }

        let alloc_end = Self::end_addr(alloc_addr, len);
        let free_end = Self::end_addr(free_addr, free_len);
        let suffix_len = free_end - alloc_end;
        if suffix_len > 0 {
            self.insert_free_block(alloc_end, suffix_len);
        }

        alloc_addr
    }

    fn clip(free_addr: Addr, free_len: usize, bounds: &Range<Addr>) -> Option<(Addr, usize)> {
        let start = free_addr.max(bounds.start);
        let end = Self::end_addr(free_addr, free_len).min(bounds.end);
        (start < end).then(|| (start, end - start))
    }

    fn fit_in_free_block(
        free_addr: Addr,
        free_len: usize,
        len: usize,
        placement: AllocationPlacement,
        alignment: usize,
        bounds: &Range<Addr>,
    ) -> Option<(Addr, usize, Addr)> {
        let (addr, clipped_len) = Self::clip(free_addr, free_len, bounds)?;
        Self::aligned_addr_in_free_block(addr, clipped_len, len, placement, alignment)
            .map(|alloc_addr| (free_addr, free_len, alloc_addr))
    }

    fn alloc_at_free_addr(
        &mut self,
        free_block: Option<(Addr, usize, Addr)>,
        len: usize,
    ) -> Result<Addr, AllocError> {
        if let Some((free_addr, free_len, alloc_addr)) = free_block {
            Ok(self.take_allocation_from_free_block(free_addr, free_len, alloc_addr, len))
        } else {
            Err(AllocError)
        }
    }

    fn alloc_best_fit(
        &mut self,
        len: usize,
        alignment: usize,
        bounds: &Range<Addr>,
        direction: AllocationDirection,
    ) -> Result<Addr, AllocError> {
        let descending = direction == AllocationDirection::Descending;
        let in_hole = if descending {
            AllocationPlacement::Top
        } else {
            AllocationPlacement::Bottom
        };
        let free_block =
            self.free_addrs_by_len
                .range(len..)
                .flat_map(|(&free_len, free_addrs)| {
                    free_addrs
                        .iter()
                        .map(move |&free_addr| (free_addr, free_len))
                })
                .filter_map(|(free_addr, free_len)| {
                    let (_, clipped_len) = Self::clip(free_addr, free_len, bounds)?;
                    Self::fit_in_free_block(free_addr, free_len, len, in_hole, alignment, bounds)
                        .map(|fit| {
                            let tie_break = if descending { !free_addr } else { free_addr };
                            ((clipped_len, tie_break), fit)
                        })
                })
                .min_by_key(|&(key, _)| key)
                .map(|(_, fit)| fit);
        self.alloc_at_free_addr(free_block, len)
    }

    fn alloc_bottom(
        &mut self,
        len: usize,
        alignment: usize,
        bounds: &Range<Addr>,
    ) -> Result<Addr, AllocError> {
        let straddling = self.free_len_by_addr.range(..bounds.start).next_back();
        let free_block = straddling
            .into_iter()
            .chain(self.free_len_by_addr.range(bounds.start..bounds.end))
            .find_map(|(&free_addr, &free_len)| {
                Self::fit_in_free_block(
                    free_addr,
                    free_len,
                    len,
                    AllocationPlacement::Bottom,
                    alignment,
                    bounds,
                )
            });
        self.alloc_at_free_addr(free_block, len)
    }

    fn alloc_top(
        &mut self,
        len: usize,
        alignment: usize,
        bounds: &Range<Addr>,
    ) -> Result<Addr, AllocError> {
        let free_block = self
            .free_len_by_addr
            .range(..bounds.end)
            .rev()
            .take_while(|&(&free_addr, &free_len)| {
                Self::end_addr(free_addr, free_len) > bounds.start
            })
            .find_map(|(&free_addr, &free_len)| {
                Self::fit_in_free_block(
                    free_addr,
                    free_len,
                    len,
                    AllocationPlacement::Top,
                    alignment,
                    bounds,
                )
            });
        self.alloc_at_free_addr(free_block, len)
    }

    pub fn alloc_aligned(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
        alignment: usize,
    ) -> Result<NonNull<u8>, AllocError> {
        let bounds = self.ptrs[0]..self.region_end(self.ptrs.len() - 1);
        self.alloc_aligned_in(
            len,
            placement,
            alignment,
            bounds,
            AllocationDirection::Ascending,
        )
    }

    pub fn alloc_aligned_in(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
        alignment: usize,
        bounds: Range<Addr>,
        direction: AllocationDirection,
    ) -> Result<NonNull<u8>, AllocError> {
        assert!(alignment.is_power_of_two());
        assert!(
            bounds.start <= bounds.end,
            "allocation bounds must not be inverted"
        );
        if len == 0 {
            return Ok(Self::ptr_from_addr(self.ptrs[0]));
        }
        let result = match (placement, direction) {
            (AllocationPlacement::BestFit, _) => {
                self.alloc_best_fit(len, alignment, &bounds, direction)
            }
            (AllocationPlacement::Bottom, AllocationDirection::Ascending)
            | (AllocationPlacement::Top, AllocationDirection::Descending) => {
                self.alloc_bottom(len, alignment, &bounds)
            }
            (AllocationPlacement::Top, AllocationDirection::Ascending)
            | (AllocationPlacement::Bottom, AllocationDirection::Descending) => {
                self.alloc_top(len, alignment, &bounds)
            }
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

impl AllocationsTracker {
    pub fn get_used_mem_peak(&self) -> usize {
        self.used_mem_peak
    }
}

#[cfg(test)]
impl AllocationsTracker {
    fn from_raw_regions(addrs_and_lens: &[(usize, usize)]) -> Self {
        Self::new_from_addrs(addrs_and_lens)
    }

    pub fn alloc(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> Result<NonNull<u8>, AllocError> {
        self.alloc_aligned(len, placement, 1)
    }
}

unsafe impl Send for AllocationsTracker {}

#[cfg(test)]
mod cpu_tests {
    use super::{AllocationDirection, AllocationPlacement, AllocationsTracker};

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

        let first = tracker
            .alloc(REGION_LEN, AllocationPlacement::Bottom)
            .unwrap();
        let second = tracker
            .alloc(REGION_LEN, AllocationPlacement::Bottom)
            .unwrap();

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

        let first = tracker
            .alloc(REGION_LEN, AllocationPlacement::Bottom)
            .unwrap();
        let second = tracker
            .alloc(REGION_LEN, AllocationPlacement::Bottom)
            .unwrap();

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

    fn alloc_in(
        tracker: &mut AllocationsTracker,
        len: usize,
        placement: AllocationPlacement,
        bounds: std::ops::Range<usize>,
    ) -> Option<usize> {
        tracker
            .alloc_aligned_in(len, placement, 1, bounds, AllocationDirection::Ascending)
            .ok()
            .map(|ptr| ptr.as_ptr() as usize)
    }

    #[test]
    fn bounded_placements_stay_within_bounds() {
        let mut tracker = tracker(&[(REGION_A, REGION_LEN)]);
        let bounds = REGION_A + 0x40..REGION_A + 0xC0;

        let bottom = alloc_in(
            &mut tracker,
            0x20,
            AllocationPlacement::Bottom,
            bounds.clone(),
        );
        let top = alloc_in(&mut tracker, 0x20, AllocationPlacement::Top, bounds.clone());
        let best_fit = alloc_in(
            &mut tracker,
            0x20,
            AllocationPlacement::BestFit,
            bounds.clone(),
        );

        assert_eq!(bottom, Some(REGION_A + 0x40));
        assert_eq!(top, Some(REGION_A + 0xA0));
        assert_eq!(best_fit, Some(REGION_A + 0x60));
        assert_free_blocks(
            &tracker,
            &[
                (REGION_A, 0x40),
                (REGION_A + 0x80, 0x20),
                (REGION_A + 0xC0, 0x40),
            ],
        );
    }

    #[test]
    fn bounded_allocation_fails_when_only_outside_space_fits() {
        let mut tracker = tracker(&[(REGION_A, REGION_LEN)]);
        let bounds = REGION_A..REGION_A + 0x40;

        for placement in [
            AllocationPlacement::Bottom,
            AllocationPlacement::Top,
            AllocationPlacement::BestFit,
        ] {
            assert_eq!(
                alloc_in(&mut tracker, 0x41, placement, bounds.clone()),
                None
            );
        }
        assert_eq!(tracker.get_used_mem_current(), 0);
        assert_free_blocks(&tracker, &[(REGION_A, REGION_LEN)]);
    }

    #[test]
    fn bounded_free_coalesces_with_space_outside_bounds() {
        let mut tracker = tracker(&[(REGION_A, REGION_LEN)]);
        let bounds = REGION_A + 0x40..REGION_A + 0x80;

        let ptr = tracker
            .alloc_aligned_in(
                0x40,
                AllocationPlacement::Top,
                1,
                bounds,
                AllocationDirection::Ascending,
            )
            .unwrap();
        assert_eq!(ptr.as_ptr() as usize, REGION_A + 0x40);
        assert_free_blocks(&tracker, &[(REGION_A, 0x40), (REGION_A + 0x80, 0x80)]);

        tracker.free(ptr, 0x40);
        assert_free_blocks(&tracker, &[(REGION_A, REGION_LEN)]);
    }

    #[test]
    fn bounded_best_fit_compares_clipped_lengths() {
        let mut tracker = tracker(&[(REGION_A, REGION_LEN)]);
        let _separator = tracker.alloc(0x10, AllocationPlacement::Bottom).unwrap();
        let lower = tracker.alloc(0x30, AllocationPlacement::Bottom).unwrap();
        let _wall = tracker.alloc(0x10, AllocationPlacement::Bottom).unwrap();
        tracker.free(lower, 0x30);
        assert_free_blocks(
            &tracker,
            &[(REGION_A + 0x10, 0x30), (REGION_A + 0x50, 0xB0)],
        );

        // Clipped to the bounds, the upper hole leaves 0x20 and beats the 0x30 hole.
        let bounds = REGION_A + 0x10..REGION_A + 0x70;
        let best_fit = alloc_in(&mut tracker, 0x20, AllocationPlacement::BestFit, bounds);
        assert_eq!(best_fit, Some(REGION_A + 0x50));
    }

    #[test]
    fn full_range_bounds_match_unbounded_allocation() {
        let regions = [(REGION_A, REGION_LEN), (REGION_B, REGION_LEN)];
        let mut unbounded = tracker(&regions);
        let mut bounded = tracker(&regions);
        let full = REGION_A..REGION_B + REGION_LEN;
        let placements = [
            AllocationPlacement::Bottom,
            AllocationPlacement::Top,
            AllocationPlacement::BestFit,
        ];
        let mut live = Vec::new();
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        for step in 0..400 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            if !live.is_empty() && state.is_multiple_of(3) {
                let (ptr, other, len) = live.swap_remove((state as usize >> 8) % live.len());
                unbounded.free(ptr, len);
                bounded.free(other, len);
                continue;
            }
            let len = 0x8 * (1 + (state as usize >> 16) % 8);
            let placement = placements[(state as usize >> 24) % 3];
            let a = unbounded.alloc(len, placement);
            let b = bounded.alloc_aligned_in(
                len,
                placement,
                1,
                full.clone(),
                AllocationDirection::Ascending,
            );
            match (a, b) {
                (Ok(a), Ok(b)) => {
                    assert_eq!(a, b, "step {step}");
                    live.push((a, b, len));
                }
                (Err(_), Err(_)) => {}
                _ => panic!("bounded and unbounded allocation disagree at step {step}"),
            }
        }
    }
    #[test]
    fn descending_direction_mirrors_ascending_layout() {
        let mut ascending = tracker(&[(REGION_A, REGION_LEN)]);
        let mut descending = tracker(&[(REGION_A, REGION_LEN)]);
        let mirror = |addr: usize, len: usize| 2 * REGION_A + REGION_LEN - addr - len;
        let placements = [
            AllocationPlacement::Bottom,
            AllocationPlacement::Top,
            AllocationPlacement::BestFit,
        ];
        let mut live = Vec::new();
        let mut state = 0x2545_f491_4f6c_dd1du64;
        for step in 0..600 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            if !live.is_empty() && state.is_multiple_of(3) {
                let (a, d, len) = live.swap_remove((state as usize >> 8) % live.len());
                ascending.free(a, len);
                descending.free(d, len);
                continue;
            }
            let len = 0x4 * (1 + (state as usize >> 16) % 6);
            let placement = placements[(state as usize >> 24) % 3];
            let start = REGION_A + 0x4 * ((state as usize >> 32) % 8);
            let end = REGION_A + REGION_LEN - 0x4 * ((state as usize >> 40) % 8);
            let a = ascending.alloc_aligned_in(
                len,
                placement,
                1,
                start..end,
                AllocationDirection::Ascending,
            );
            let d = descending.alloc_aligned_in(
                len,
                placement,
                1,
                mirror(end, 0)..mirror(start, 0),
                AllocationDirection::Descending,
            );
            match (a, d) {
                (Ok(a), Ok(d)) => {
                    assert_eq!(
                        mirror(a.as_ptr() as usize, len),
                        d.as_ptr() as usize,
                        "step {step}"
                    );
                    live.push((a, d, len));
                }
                (Err(_), Err(_)) => {}
                _ => panic!("mirrored allocation disagrees at step {step}"),
            }
        }
    }
}
