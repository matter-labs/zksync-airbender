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

    /// Permanently reserve cells [0, cells) for the pinned prefix. Must be
    /// called before any alloc. Pinned cells are addressed directly by the
    /// caller and never released.
    pub fn reserve_prefix(&mut self, cells: usize) {
        assert!(cells <= self.free.len(), "pinned prefix {cells} exceeds budget {}", self.free.len());
        debug_assert!(self.high_water_cells == 0, "reserve_prefix after alloc");
        self.free[..cells].iter_mut().for_each(|f| *f = false);
        self.high_water_cells = cells;
    }

    /// Currently-free cell count (capacity check for optional loads).
    pub fn free_cells(&self) -> usize {
        self.free.iter().filter(|f| **f).count()
    }

    /// Fragmentation-immune allocation for the forward compiler ONLY (the
    /// cone compiler keeps the original first-fit so its validated numbers
    /// are untouched). Two-ended regions over the shared free map: bf cells
    /// (width 1) fill bottom-up, packing into already-dirty quads first; e4
    /// quads (width 4, aligned) fill top-down. bf churn therefore can never
    /// scatter single cells across the quads e4 needs — alignment starvation
    /// (free cells exist but no free aligned quad) becomes impossible until
    /// the regions genuinely collide, i.e. true capacity exhaustion.
    pub fn alloc_packed(&mut self, width_cells: usize) -> Option<u16> {
        if width_cells == 1 {
            // Pass 1: a free cell inside a dirty quad (bottom-up).
            let mut c = 0;
            while c + 4 <= self.free.len() {
                let quad = &self.free[c..c + 4];
                if quad.iter().any(|f| !*f) {
                    if let Some(k) = quad.iter().position(|f| *f) {
                        self.free[c + k] = false;
                        self.high_water_cells = self.high_water_cells.max(c + k + 1);
                        return Some((c + k) as u16);
                    }
                }
                c += 4;
            }
            // Pass 2: first-fit (clean quads / tail cells).
            return self.alloc(1);
        }
        debug_assert_eq!(width_cells, 4, "forward widths are 1 or 4");
        if self.free.len() < 4 {
            return None;
        }
        // e4: topmost free aligned quad, scanning down.
        let mut c = (self.free.len() / 4).saturating_sub(1) * 4;
        loop {
            if self.free[c..c + 4].iter().all(|f| *f) {
                self.free[c..c + 4].iter_mut().for_each(|f| *f = false);
                self.high_water_cells = self.high_water_cells.max(c + 4);
                return Some(c as u16);
            }
            if c == 0 {
                return None;
            }
            c -= 4;
        }
    }

    pub fn release(&mut self, cell: u16, width_cells: usize) {
        let c = cell as usize;
        debug_assert!(c + width_cells <= self.free.len());
        debug_assert!(self.free[c..c + width_cells].iter().all(|f| !*f), "double free or wrong width");
        self.free[c..c + width_cells].iter_mut().for_each(|f| *f = true);
    }

}
