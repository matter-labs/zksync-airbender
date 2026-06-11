//! Slot-file allocator. Task 5: first-fit free list, panics when over budget.
//! Task 7 replaces the panic with Belady eviction + rematerialization.

pub struct SlotAlloc {
    free: Vec<bool>, // free[cell]
    /// Max cell address ever allocated + width (exact buffer size needed).
    /// Address-based: tracks the highest cell address touched, not the peak
    /// live count. Fragmentation can place cells above the live count, so
    /// only an address-based high water correctly sizes the interpreter buffer.
    pub high_water_cells: usize,
}

impl SlotAlloc {
    pub fn new(budget_cells: usize) -> Self {
        SlotAlloc { free: vec![true; budget_cells], high_water_cells: 0 }
    }

    /// width_cells = 1 (bf) or 4 (e4, kept 4-aligned).
    pub fn alloc(&mut self, width_cells: usize) -> Option<u16> {
        let step = width_cells;
        let mut c = 0;
        while c + width_cells <= self.free.len() {
            if self.free[c..c + width_cells].iter().all(|f| *f) {
                self.free[c..c + width_cells].iter_mut().for_each(|f| *f = false);
                self.high_water_cells = self.high_water_cells.max(c + width_cells);
                return Some(c as u16);
            }
            c += step;
        }
        None
    }

    /// Total slot capacity (cells), as passed to `new`.
    pub fn budget(&self) -> usize {
        self.free.len()
    }

    pub fn release(&mut self, cell: u16, width_cells: usize) {
        let c = cell as usize;
        debug_assert!(c + width_cells <= self.free.len());
        debug_assert!(self.free[c..c + width_cells].iter().all(|f| !*f), "double free or wrong width");
        self.free[c..c + width_cells].iter_mut().for_each(|f| *f = true);
    }

}
