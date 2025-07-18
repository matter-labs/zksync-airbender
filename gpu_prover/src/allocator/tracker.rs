use itertools::Itertools;
use std::alloc::AllocError;
use std::collections::{BTreeMap, BTreeSet, Bound};
use std::ptr::NonNull;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocationPlacement {
    BestFit,
    Bottom,
    Top,
}

pub struct AllocationsTracker {
    ptrs: Vec<NonNull<u8>>,
    lens: Vec<usize>,
    free_len_by_ptr: BTreeMap<NonNull<u8>, usize>,
    free_ptrs_by_len: BTreeMap<usize, BTreeSet<NonNull<u8>>>,
    used_mem_current: usize,
    used_mem_peak: usize,
}

impl AllocationsTracker {
    pub fn new(ptrs_and_lens: &[(NonNull<u8>, usize)]) -> Self {
        let len = ptrs_and_lens.len();
        let mut ptrs = Vec::with_capacity(len);
        let mut lens = Vec::with_capacity(len);
        let mut free_len_by_ptr = BTreeMap::new();
        let mut free_ptrs_by_len = BTreeMap::new();
        for &(ptr, len) in ptrs_and_lens.iter().sorted() {
            ptrs.push(ptr);
            lens.push(len);
            assert!(
                free_len_by_ptr.insert(ptr, len).is_none(),
                "duplicate pointer"
            );
            let ptrs = free_ptrs_by_len.entry(len).or_insert_with(BTreeSet::new);
            ptrs.insert(ptr);
        }
        Self {
            ptrs,
            lens,
            free_len_by_ptr,
            free_ptrs_by_len,
            used_mem_current: 0,
            used_mem_peak: 0,
        }
    }

    fn insert_remainder(
        &mut self,
        free_ptr: NonNull<u8>,
        free_len: usize,
        len: usize,
        placement: AllocationPlacement,
    ) -> NonNull<u8> {
        assert!(free_len > len);
        let free_len = free_len - len;
        let (ptr, free_ptr) = unsafe {
            match placement {
                AllocationPlacement::Top => (free_ptr.add(free_len), free_ptr),
                _ => (free_ptr, free_ptr.add(len)),
            }
        };
        assert!(self.free_len_by_ptr.insert(free_ptr, free_len).is_none());
        assert!(self
            .free_ptrs_by_len
            .entry(free_len)
            .or_default()
            .insert(free_ptr));
        ptr
    }

    fn alloc_best_fit(&mut self, len: usize) -> Result<NonNull<u8>, AllocError> {
        let mut cursor = self.free_ptrs_by_len.lower_bound_mut(Bound::Included(&len));
        if let Some((&free_len, free_ptrs)) = cursor.peek_next() {
            let free_ptr = free_ptrs.pop_first().unwrap();
            if free_ptrs.is_empty() {
                cursor.remove_next();
            }
            assert_eq!(self.free_len_by_ptr.remove(&free_ptr).unwrap(), free_len);
            if free_len > len {
                self.insert_remainder(free_ptr, free_len, len, AllocationPlacement::BestFit);
            }
            Ok(free_ptr)
        } else {
            Err(AllocError)
        }
    }

    fn find_free_ptr_by_len<'a>(
        mut iter: impl Iterator<Item = (&'a NonNull<u8>, &'a usize)>,
        len: usize,
    ) -> Option<NonNull<u8>> {
        iter.find_map(|(&ptr, &l)| if l >= len { Some(ptr) } else { None })
    }

    fn alloc_at_free_ptr(
        &mut self,
        free_ptr: Option<NonNull<u8>>,
        len: usize,
        placement: AllocationPlacement,
    ) -> Result<NonNull<u8>, AllocError> {
        if let Some(free_ptr) = free_ptr {
            let free_len = self.free_len_by_ptr.remove(&free_ptr).unwrap();
            assert!(free_len >= len);
            let ptrs = self.free_ptrs_by_len.get_mut(&free_len).unwrap();
            assert!(ptrs.remove(&free_ptr));
            if ptrs.is_empty() {
                assert!(self.free_ptrs_by_len.remove(&free_len).unwrap().is_empty());
            }
            Ok(if free_len == len {
                free_ptr
            } else {
                self.insert_remainder(free_ptr, free_len, len, placement)
            })
        } else {
            Err(AllocError)
        }
    }

    fn alloc_bottom(&mut self, len: usize) -> Result<NonNull<u8>, AllocError> {
        let iter = self.free_len_by_ptr.iter();
        let free_ptr = Self::find_free_ptr_by_len(iter, len);
        self.alloc_at_free_ptr(free_ptr, len, AllocationPlacement::Bottom)
    }

    fn alloc_top(&mut self, len: usize) -> Result<NonNull<u8>, AllocError> {
        let free_ptr = Self::find_free_ptr_by_len(self.free_len_by_ptr.iter().rev(), len);
        self.alloc_at_free_ptr(free_ptr, len, AllocationPlacement::Top)
    }

    pub fn alloc(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> Result<NonNull<u8>, AllocError> {
        let result = match placement {
            AllocationPlacement::BestFit => self.alloc_best_fit(len),
            AllocationPlacement::Bottom => self.alloc_bottom(len),
            AllocationPlacement::Top => self.alloc_top(len),
        };
        if result.is_ok() {
            self.used_mem_current += len;
            self.used_mem_peak = self.used_mem_peak.max(self.used_mem_current);
        };
        result
    }

    pub fn free(&mut self, mut ptr: NonNull<u8>, mut len: usize) {
        assert_ne!(len, 0, "attempt to free zero-length allocation");
        self.used_mem_current -= len;
        unsafe {
            let idx = match self.ptrs.binary_search(&ptr) {
                Ok(idx) => idx,
                Err(0) => panic!("out of bounds free"),
                Err(idx) => idx - 1,
            };
            let self_ptr = self.ptrs[idx];
            let self_len = self.lens[idx];
            let offset = ptr.offset_from(self_ptr);
            assert!(
                offset >= 0 && (offset as usize + len) <= self_len,
                "out of bounds free"
            );
            let mut cursor = self.free_len_by_ptr.lower_bound_mut(Bound::Included(&ptr));
            if let Some((&next_ptr, &mut next_len)) = cursor.peek_next() {
                let offset = next_ptr.offset_from(ptr);
                assert!(offset >= len as isize, "double free");
                if offset as usize == len && ptr.add(len) != self_ptr.add(self_len) {
                    cursor.remove_next();
                    let ptrs = self.free_ptrs_by_len.get_mut(&next_len).unwrap();
                    assert!(ptrs.remove(&next_ptr));
                    if ptrs.is_empty() {
                        assert!(self.free_ptrs_by_len.remove(&next_len).unwrap().is_empty());
                    }
                    len += next_len;
                }
            }
            if let Some((&prev_ptr, &mut prev_len)) = cursor.peek_prev() {
                let offset = ptr.offset_from(prev_ptr);
                assert!(offset >= prev_len as isize, "double free");
                if offset as usize == prev_len && ptr != self_ptr {
                    cursor.remove_prev();
                    let ptrs = self.free_ptrs_by_len.get_mut(&prev_len).unwrap();
                    assert!(ptrs.remove(&prev_ptr));
                    if ptrs.is_empty() {
                        assert!(self.free_ptrs_by_len.remove(&prev_len).unwrap().is_empty());
                    }
                    ptr = prev_ptr;
                    len += prev_len;
                }
            }
        }
        self.free_len_by_ptr.insert(ptr, len);
        self.free_ptrs_by_len.entry(len).or_default().insert(ptr);
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
}

unsafe impl Send for AllocationsTracker {}
