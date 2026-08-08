//! Host mirror of the device wire in `native/uniskip_abi.cuh`.
//!
//! Every constant, struct layout and address computation here is pinned against
//! the header's `static_assert`s by `cpu_abi_layout`.

/// Direct taps of a logical row, living on `H` (k = 4).
pub const UNISKIP_TAPS: usize = 16;
/// `log2(UNISKIP_TAPS)` — the k = 4 skip factor, `log_trace - log_rows`.
pub const UNISKIP_LOG_TAPS: u32 = UNISKIP_TAPS.trailing_zeros();
/// Cells evaluated per logical row: `0..16` on `H`, `16..32` on the coset.
pub const UNISKIP_CELLS: usize = 32;

pub const UNISKIP_THREADS_PER_BLOCK: usize = 256;
pub const UNISKIP_WARPS_PER_BLOCK: usize = 8;
pub const UNISKIP_CELLS_PER_WARP: usize = 4;
/// Rows a block covers: one lane per row, `UNISKIP_THREADS_PER_BLOCK / UNISKIP_WARPS_PER_BLOCK`.
pub const UNISKIP_ROWS_PER_BLOCK: usize = UNISKIP_THREADS_PER_BLOCK / UNISKIP_WARPS_PER_BLOCK;

/// v3 LSB launch geometry: a warp owns two GROUPS, one per half-warp, and lane `t` of
/// a half-warp owns tap `t` of its group — so the group is a 16-lane segment and a
/// block covers `UNISKIP_WARPS_PER_BLOCK * 2` logical rows, not 32.
pub const UNISKIP_LSB_GROUPS_PER_WARP: usize = 32 / UNISKIP_TAPS;
pub const UNISKIP_LSB_ROWS_PER_BLOCK: usize = UNISKIP_WARPS_PER_BLOCK * UNISKIP_LSB_GROUPS_PER_WARP;

/// Lane-indexed twiddle tables of the factorized coset transform — see
/// [`crate::domain::ntt_twiddles`] for the stage order. The two distance-1 butterfly
/// stages carry only unity and are elided, so the chain's 8 exchange stages need 7
/// multiplier tables.
pub const UNISKIP_NTT_TABLES: usize = 7;

pub const UNISKIP_WINDOWS: usize = 6;
pub const UNISKIP_SOURCE_CAPACITY: usize = 64;
pub const UNISKIP_PROGRAM_CAPACITY: usize = 256;
pub const UNISKIP_COEFF_BANK: usize = 128;
pub const UNISKIP_EQ_HIGH: usize = 256;
/// `log2(UNISKIP_EQ_HIGH)` — the per-table cap on an eq high group's bit count.
pub const UNISKIP_LOG_EQ_HIGH: u32 = 8;

pub const UNISKIP_CLASS_LINEAR_BF: u16 = 0;
pub const UNISKIP_CLASS_LINEAR_E4: u16 = 1;
pub const UNISKIP_CLASS_PRODUCT_BF_BF: u16 = 2;
pub const UNISKIP_CLASS_PRODUCT_BF_E4: u16 = 3;
pub const UNISKIP_CLASS_PRODUCT_E4_E4: u16 = 4;
pub const UNISKIP_CLASS_GROUP_BF: u16 = 5;

pub const UNISKIP_IMMEDIATE_ONE: u16 = 0;
pub const UNISKIP_IMMEDIATE_NEG_ONE: u16 = 1;
pub const UNISKIP_IMMEDIATE_RESERVED: u16 = 2;
pub const UNISKIP_MAX_IMMEDIATES: usize = 16;

pub const UNISKIP_SRC_BF_GLOBAL: u8 = 0;
pub const UNISKIP_SRC_E4_GLOBAL: u8 = 1;

pub const UNISKIP_SOURCE_UNUSED: u16 = 0xffff;

/// `u32` words of one shared-memory cache unit: one `bf` plane of a source's coset
/// slab for a block's row tile — `UNISKIP_TAPS` coset cells by
/// `UNISKIP_ROWS_PER_BLOCK` rows.
pub const UNISKIP_CACHE_UNIT_WORDS: usize = UNISKIP_TAPS * UNISKIP_ROWS_PER_BLOCK;
/// Units the fused-cached kernel's shared pool holds. A `bf` source takes one, an
/// `e4` source four (one per limb), so a slab's byte cost is exactly its component
/// width times [`UNISKIP_CACHE_UNIT_WORDS`].
pub const UNISKIP_CACHE_UNITS: usize = 16;
pub const UNISKIP_CACHE_POOL_WORDS: usize = UNISKIP_CACHE_UNITS * UNISKIP_CACHE_UNIT_WORDS;
pub const UNISKIP_CACHE_UNIT_BYTES: usize = UNISKIP_CACHE_UNIT_WORDS * size_of::<u32>();
/// [`UniskipSourceRecord::cache_slot`] of an uncached source.
pub const UNISKIP_CACHE_SLOT_NONE: u8 = 0xff;
/// Entry of a free unit in the inverse (unit -> source) fill plan.
pub const UNISKIP_CACHE_FILL_NONE: u16 = 0xffff;

/// `bf` limbs of one element of a source class — the component width the cache plan
/// prices slabs and resolver work in.
pub const fn component_width(source_class: u8) -> u32 {
    match source_class {
        UNISKIP_SRC_E4_GLOBAL => 4,
        _ => 1,
    }
}

/// `addr = window << UNISKIP_ADDR_COLUMN_BITS | column`.
pub const UNISKIP_ADDR_COLUMN_BITS: u32 = 7;
pub const UNISKIP_ADDR_COLUMN_MASK: u16 = (1 << UNISKIP_ADDR_COLUMN_BITS) - 1;
/// Columns a single window can address.
pub const UNISKIP_MAX_WINDOW_COLUMNS: usize = 1 << UNISKIP_ADDR_COLUMN_BITS;

/// Planes an `addr` can name: `UNISKIP_MAX_WINDOW_COLUMNS * UNISKIP_TAPS`. The
/// accessor's element index is `(plane << log_rows) + row`, so it occupies
/// `UNISKIP_LOG_ADDRESSABLE_PLANES + log_rows` bits.
pub const UNISKIP_LOG_ADDRESSABLE_PLANES: u32 = UNISKIP_ADDR_COLUMN_BITS + UNISKIP_LOG_TAPS;
/// The device `load()` takes a 32-bit `unsigned` offset, which is what bounds
/// `log_rows` (see `geometry::UNISKIP_MAX_LOG_ROWS`).
pub const UNISKIP_ELEMENT_INDEX_BITS: u32 = 32;

#[repr(C, align(8))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UniskipTerm {
    pub term_class: u16,
    /// Coefficient-bank id, or — inside a group — an immediate id.
    pub coeff: u16,
    /// Source id, or — on a group header — the member arity.
    pub source_a: u16,
    pub source_b: u16,
}

#[repr(C, align(4))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UniskipSourceRecord {
    pub addr: u16,
    pub source_class: u8,
    /// v1's `reserved` byte, same 4-byte record: the first shared-memory cache unit
    /// of this source's coset slab, or [`UNISKIP_CACHE_SLOT_NONE`] when uncached.
    /// Only the fused-cached accessor reads it.
    pub cache_slot: u8,
}

#[repr(C, align(8))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UniskipBaseRecord {
    /// Device address of the window's tap (or coset) allocation.
    pub base: u64,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UniskipEqSizes {
    pub high: [u32; 2],
    pub low: u32,
}

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug)]
pub struct UniskipVmDesc {
    pub program: [UniskipTerm; UNISKIP_PROGRAM_CAPACITY],
    pub source: [UniskipSourceRecord; UNISKIP_SOURCE_CAPACITY],
    pub tap_bases: [UniskipBaseRecord; UNISKIP_WINDOWS],
    pub coset_bases: [UniskipBaseRecord; UNISKIP_WINDOWS],
    /// Device representation, not canonical — see `SynthProgram::immediates_canonical`.
    pub immediates: [u32; UNISKIP_MAX_IMMEDIATES],
    pub eq_low: u64,
    pub partials: u64,
    pub record_count: u32,
    pub num_sources: u32,
    pub log_rows: u32,
    pub eq_sizes: UniskipEqSizes,
}

impl Default for UniskipVmDesc {
    fn default() -> Self {
        Self {
            program: [UniskipTerm::default(); UNISKIP_PROGRAM_CAPACITY],
            source: [UniskipSourceRecord::default(); UNISKIP_SOURCE_CAPACITY],
            tap_bases: [UniskipBaseRecord::default(); UNISKIP_WINDOWS],
            coset_bases: [UniskipBaseRecord::default(); UNISKIP_WINDOWS],
            immediates: [0; UNISKIP_MAX_IMMEDIATES],
            eq_low: 0,
            partials: 0,
            record_count: 0,
            num_sources: 0,
            log_rows: 0,
            eq_sizes: UniskipEqSizes::default(),
        }
    }
}

pub const fn source_addr(window: usize, column: usize) -> u16 {
    ((window as u16) << UNISKIP_ADDR_COLUMN_BITS) | column as u16
}

pub const fn addr_window(addr: u16) -> usize {
    (addr >> UNISKIP_ADDR_COLUMN_BITS) as usize
}

pub const fn addr_column(addr: u16) -> usize {
    (addr & UNISKIP_ADDR_COLUMN_MASK) as usize
}

/// Which of a window's two allocations a cell reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CellBuffer {
    /// The 16 taps on `H`.
    Tap,
    /// The 16 cells of `gamma * H`.
    Coset,
}

/// CELL NUMBERING CONTRACT: tap `t` is cell `t`; row `c` of `domain::lde_matrix()`
/// — the coset cell `gamma * omega^c` — is cell `UNISKIP_TAPS + c`. Host code that
/// flattens the LDE matrix, and device code that branches on `cell >= UNISKIP_TAPS`,
/// both hang off these two functions.
pub const fn cell_for_tap(tap: usize) -> usize {
    tap
}

pub const fn cell_for_coset_row(coset_row: usize) -> usize {
    UNISKIP_TAPS + coset_row
}

/// Inverse of [`cell_for_coset_row`]; `None` for the tap cells.
pub const fn coset_row_for_cell(cell: usize) -> Option<usize> {
    if cell >= UNISKIP_TAPS {
        Some(cell - UNISKIP_TAPS)
    } else {
        None
    }
}

pub const fn cell_buffer(cell: usize) -> CellBuffer {
    match coset_row_for_cell(cell) {
        Some(_) => CellBuffer::Coset,
        None => CellBuffer::Tap,
    }
}

/// Element ordering inside a column's backing. Both orderings pack windows into one
/// allocation per field class the same way and give a column the same
/// `UNISKIP_TAPS << log_rows` elements; they differ only in where a `(row, tap)` pair
/// sits inside that block.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SourceLayout {
    /// v1/v2, plane-major (MSB): tap `t` of row `r` is at `r + (t << log_rows)`, so a
    /// tap is a plane and a warp of consecutive rows is contiguous.
    #[default]
    PlaneMajor,
    /// v3, LSB lane-striped: tap `t` of row `r` is at `(r << 4) | t`, so the 16 taps
    /// of one row are 16 ADJACENT elements — one group, one coalesced half-warp load.
    /// There is no coset allocation in this ordering.
    LsbGroup,
}

/// Host mirror of the LSB accessor's address arithmetic: the element offset of one
/// tap of `(source, row)` inside its window, `column * (16 << log_rows) + (row << 4) + tap`.
/// The addressing bound is unchanged — the largest index is still
/// `2^(UNISKIP_LOG_ADDRESSABLE_PLANES + log_rows) - 1`, just reached by a different
/// decomposition.
pub fn lsb_source_offset(rec: UniskipSourceRecord, tap: usize, row: u64, log_rows: u32) -> u64 {
    assert!(tap < UNISKIP_TAPS, "tap {tap} out of range");
    let group = ((addr_column(rec.addr) as u64) << log_rows) + row;
    (group << UNISKIP_LOG_TAPS) + tap as u64
}

/// Host mirror of `uniskip_source_value`'s address arithmetic: the allocation a
/// `(source, cell)` pair reads and the element offset of `row` inside it.
pub fn source_offset(
    rec: UniskipSourceRecord,
    cell: usize,
    row: u64,
    log_rows: u32,
) -> (CellBuffer, u64) {
    assert!(cell < UNISKIP_CELLS, "cell {cell} out of range");
    let local = match coset_row_for_cell(cell) {
        Some(c) => c,
        None => cell,
    };
    let plane = addr_column(rec.addr) * UNISKIP_TAPS + local;
    (cell_buffer(cell), ((plane as u64) << log_rows) + row)
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::synth::{generate, Census, WindowKind};
    use core::mem::{align_of, offset_of, size_of};

    #[test]
    fn cpu_abi_layout() {
        assert_eq!(size_of::<UniskipTerm>(), 8);
        assert_eq!(align_of::<UniskipTerm>(), 8);
        assert_eq!(size_of::<UniskipSourceRecord>(), 4);
        assert_eq!(align_of::<UniskipSourceRecord>(), 4);
        assert_eq!(size_of::<UniskipBaseRecord>(), 8);
        assert_eq!(align_of::<UniskipBaseRecord>(), 8);
        assert_eq!(size_of::<UniskipEqSizes>(), 12);

        assert_eq!(offset_of!(UniskipVmDesc, program), 0);
        assert_eq!(offset_of!(UniskipVmDesc, source), 2048);
        assert_eq!(offset_of!(UniskipVmDesc, tap_bases), 2304);
        assert_eq!(offset_of!(UniskipVmDesc, coset_bases), 2352);
        assert_eq!(offset_of!(UniskipVmDesc, immediates), 2400);
        assert_eq!(offset_of!(UniskipVmDesc, eq_low), 2464);
        assert_eq!(offset_of!(UniskipVmDesc, partials), 2472);
        assert_eq!(offset_of!(UniskipVmDesc, record_count), 2480);
        assert_eq!(offset_of!(UniskipVmDesc, num_sources), 2484);
        assert_eq!(offset_of!(UniskipVmDesc, log_rows), 2488);
        assert_eq!(offset_of!(UniskipVmDesc, eq_sizes), 2492);
        assert_eq!(size_of::<UniskipVmDesc>(), 2512);
        assert_eq!(align_of::<UniskipVmDesc>(), 16);
        assert!(size_of::<UniskipVmDesc>() <= 32764);

        // Launch geometry, mirrored from the header's constants of the same name:
        // one warp-wide row tile per block, so `lane == row - blockIdx * 32`.
        assert_eq!(UNISKIP_ROWS_PER_BLOCK, 32);
        // v3 LSB geometry: a 16-lane half-warp is one group, so a block is 16 rows.
        assert_eq!(UNISKIP_LSB_GROUPS_PER_WARP, 2);
        assert_eq!(UNISKIP_LSB_ROWS_PER_BLOCK, 16);
        assert_eq!(UNISKIP_NTT_TABLES, 7);

        // Addressing bound, mirrored from the header's constants of the same name.
        assert_eq!(UNISKIP_LOG_TAPS, 4);
        assert_eq!(UNISKIP_LOG_ADDRESSABLE_PLANES, 11);
        assert_eq!(UNISKIP_ELEMENT_INDEX_BITS, 32);
        assert_eq!(
            1usize << UNISKIP_LOG_ADDRESSABLE_PLANES,
            UNISKIP_MAX_WINDOW_COLUMNS * UNISKIP_TAPS
        );

        // __constant__ budget: coeff bank + both eq high tables + LDE matrix + fold
        // weights + the inverse cache-fill plan.
        let constant_bytes = UNISKIP_COEFF_BANK * 16
            + 2 * UNISKIP_EQ_HIGH * 16
            + UNISKIP_TAPS * UNISKIP_TAPS * 4
            + UNISKIP_TAPS * 16
            + UNISKIP_CACHE_UNITS * 2;
        assert!(
            constant_bytes <= 64 * 1024,
            "{constant_bytes} B of __constant__"
        );

        // Shared-memory cache, mirrored from the header's constants of the same name.
        assert_eq!(UNISKIP_CACHE_UNIT_WORDS, 512);
        assert_eq!(UNISKIP_CACHE_UNIT_BYTES, 2048);
        assert_eq!(UNISKIP_CACHE_POOL_WORDS * 4, 32768);
        const { assert!(UNISKIP_CACHE_POOL_WORDS * 4 <= 48 * 1024, "static smem cap") };
        const { assert!(UNISKIP_CACHE_UNITS < UNISKIP_CACHE_SLOT_NONE as usize) };
        const {
            assert!(
                UNISKIP_SOURCE_CAPACITY <= 0x100,
                "fill entry packs a source id"
            )
        };
        assert_eq!(
            (UNISKIP_CACHE_UNITS * UNISKIP_ROWS_PER_BLOCK) % UNISKIP_THREADS_PER_BLOCK,
            0
        );
        assert_eq!(component_width(UNISKIP_SRC_BF_GLOBAL), 1);
        assert_eq!(component_width(UNISKIP_SRC_E4_GLOBAL), 4);
    }

    #[test]
    fn cpu_cell_numbering() {
        assert_eq!(UNISKIP_CELLS, 2 * UNISKIP_TAPS);
        for t in 0..UNISKIP_TAPS {
            assert_eq!(cell_for_tap(t), t);
            assert_eq!(cell_buffer(cell_for_tap(t)), CellBuffer::Tap);
            assert_eq!(coset_row_for_cell(cell_for_tap(t)), None);
        }
        for c in 0..UNISKIP_TAPS {
            let cell = cell_for_coset_row(c);
            assert_eq!(cell, UNISKIP_TAPS + c);
            assert_eq!(cell_buffer(cell), CellBuffer::Coset);
            assert_eq!(coset_row_for_cell(cell), Some(c));
        }
        // The two families tile 0..UNISKIP_CELLS exactly once.
        let mut seen = [false; UNISKIP_CELLS];
        for t in 0..UNISKIP_TAPS {
            seen[cell_for_tap(t)] = true;
        }
        for c in 0..UNISKIP_TAPS {
            seen[cell_for_coset_row(c)] = true;
        }
        assert!(seen.iter().all(|&s| s));
    }

    #[test]
    fn cpu_lsb_addressing_bijection() {
        let log_trace = 10u32;
        let log_rows = log_trace - 4;
        let rows = 1u64 << log_rows;
        let columns = 5usize;

        let mut seen = std::collections::HashSet::new();
        for column in 0..columns {
            let rec = UniskipSourceRecord {
                addr: source_addr(0, column),
                source_class: UNISKIP_SRC_BF_GLOBAL,
                cache_slot: UNISKIP_CACHE_SLOT_NONE,
            };
            for row in 0..rows {
                for tap in 0..UNISKIP_TAPS {
                    let offset = lsb_source_offset(rec, tap, row, log_rows);
                    // A group is 16 ADJACENT elements, one logical row of one column.
                    assert_eq!(
                        offset,
                        column as u64 * ((UNISKIP_TAPS as u64) << log_rows)
                            + (row << UNISKIP_LOG_TAPS)
                            + tap as u64
                    );
                    assert_eq!(offset >> UNISKIP_LOG_TAPS, offset / UNISKIP_TAPS as u64);
                    assert!(seen.insert(offset));
                }
            }
        }
        // Tiles the same column block the plane-major ordering does, no gaps.
        assert_eq!(
            seen.len() as u64,
            columns as u64 * UNISKIP_TAPS as u64 * rows
        );
        assert_eq!(
            seen.iter().copied().max().unwrap() + 1,
            columns as u64 * UNISKIP_TAPS as u64 * rows
        );

        // Addressing bound: the widest legal geometry still fits the device load()'s
        // 32-bit element offset, exactly as the plane-major ordering does.
        let widest = crate::geometry::UNISKIP_MAX_LOG_ROWS;
        let last = UniskipSourceRecord {
            addr: source_addr(0, UNISKIP_MAX_WINDOW_COLUMNS - 1),
            source_class: UNISKIP_SRC_BF_GLOBAL,
            cache_slot: UNISKIP_CACHE_SLOT_NONE,
        };
        let max = lsb_source_offset(last, UNISKIP_TAPS - 1, (1 << widest) - 1, widest);
        assert_eq!(max, (1u64 << (UNISKIP_LOG_ADDRESSABLE_PLANES + widest)) - 1);
        assert!(max <= u64::from(u32::MAX));
    }

    #[test]
    fn cpu_addressing_bijection() {
        let log_trace = 10u32;
        let log_rows = log_trace - 4;
        let program = generate(7, Census::default()).unwrap();
        let rows = [0u64, 1, 17, (1 << log_rows) - 1];

        for (window, spec) in program.windows.iter().enumerate() {
            let first = 0;
            let last = spec.columns as usize - 1;
            let field_kind = spec.kind;
            for &column in &[first, last] {
                let rec = program
                    .sources
                    .iter()
                    .copied()
                    .find(|r| addr_window(r.addr) == window && addr_column(r.addr) == column)
                    .unwrap();
                assert_eq!(rec.addr, source_addr(window, column));
                assert_eq!(
                    rec.source_class,
                    if field_kind == WindowKind::E4 {
                        UNISKIP_SRC_E4_GLOBAL
                    } else {
                        UNISKIP_SRC_BF_GLOBAL
                    }
                );
                for cell in 0..UNISKIP_CELLS {
                    for &row in &rows {
                        let (buffer, offset) = source_offset(rec, cell, row, log_rows);
                        let local = match coset_row_for_cell(cell) {
                            Some(c) => {
                                assert_eq!(buffer, CellBuffer::Coset);
                                assert_eq!(cell, cell_for_coset_row(c));
                                c
                            }
                            None => {
                                assert_eq!(buffer, CellBuffer::Tap);
                                cell
                            }
                        };
                        let expected =
                            ((column as u64) << log_trace) + ((local as u64) << log_rows) + row;
                        assert_eq!(
                            offset, expected,
                            "window {window} column {column} cell {cell} row {row}"
                        );
                    }
                }
            }
        }

        // Injectivity of (column, cell, row) -> (buffer, offset) over a whole window.
        let window = 0;
        let columns = program.windows[window].columns as usize;
        let mut seen = std::collections::HashSet::new();
        for column in 0..columns {
            let rec = UniskipSourceRecord {
                addr: source_addr(window, column),
                source_class: UNISKIP_SRC_BF_GLOBAL,
                cache_slot: UNISKIP_CACHE_SLOT_NONE,
            };
            for cell in 0..UNISKIP_CELLS {
                for row in 0..(1u64 << log_rows) {
                    assert!(
                        seen.insert(source_offset(rec, cell, row, log_rows)),
                        "collision at ({column}, {cell}, {row})"
                    );
                }
            }
        }
        assert_eq!(seen.len(), columns * UNISKIP_CELLS * (1 << log_rows));
    }
}
