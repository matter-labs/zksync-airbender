//! Host reference for the device init generator and the coset LDE.
//!
//! Bit-exactness, not just algebraic agreement: every value here is compared
//! against the device word for word, so the canonical -> Montgomery conversion
//! must be the one `bf::from_u32_unchecked` performs on the device.

use field::{Field, FieldExtension};

use crate::abi::*;
use crate::domain::{lde_matrix, E4, F};
use crate::harness::{class_index, Layout, CLASS_BF, CLASS_E4, CLASS_WORDS};

/// Mirrors `uniskip_init_canonical`: `index` is the ABSOLUTE index of the field
/// element inside its backing allocation, `component` tags the `bf` limbs of an
/// `e4`. Canonical, in `[1, ORDER - 1]`, never zero.
pub fn init_canonical(seed: u32, index: u64, component: u32) -> u32 {
    const ORDER_MINUS_ONE: u64 = (F::ORDER - 1) as u64;
    ((u64::from(seed) + index * 17 + u64::from(component) * 0x101) % ORDER_MINUS_ONE + 1) as u32
}

/// Canonical `u32` -> the device's `bf` representation. `F::new` is the same
/// Montgomery lift as `bf::from_u32_unchecked`, and both leave the limb fully
/// reduced, so the raw words match bit for bit.
pub fn to_device_bf(canonical: u32) -> u32 {
    F::new(canonical).raw_u32_value()
}

pub fn init_bf(seed: u32, index: u64) -> F {
    F::new(init_canonical(seed, index, 0))
}

pub fn init_e4(seed: u32, index: u64) -> E4 {
    E4::from_array_of_base(core::array::from_fn(|c| {
        F::new(init_canonical(seed, index, c as u32))
    }))
}

/// Row `c` of the LDE matrix at `[c * UNISKIP_TAPS + t]` — the order the kernels
/// index, where `c` is the coset plane that [`cell_for_coset_row`] names cell
/// `UNISKIP_TAPS + c`.
pub fn flat_lde_matrix(
    matrix: &[[F; UNISKIP_TAPS]; UNISKIP_TAPS],
) -> [u32; UNISKIP_TAPS * UNISKIP_TAPS] {
    core::array::from_fn(|i| matrix[i / UNISKIP_TAPS][i % UNISKIP_TAPS].raw_u32_value())
}

/// Both eq high tables as one allocation of `2 * UNISKIP_EQ_HIGH` `e4` entries:
/// table 0 first, table 1 from `UNISKIP_EQ_HIGH`. Synthetic weights — they carry
/// the production factored shape, not a transcript-real `q`.
pub fn eq_high_words(seed: u32) -> [[u32; 4]; 2 * UNISKIP_EQ_HIGH] {
    core::array::from_fn(|i| e4_words(init_e4(seed, i as u64)))
}

fn e4_words(x: E4) -> [u32; 4] {
    [x.c0.c0, x.c0.c1, x.c1.c0, x.c1.c1].map(|f| f.raw_u32_value())
}

/// The two field classes a window backing can hold, spelled so the tap/LDE
/// reproduction is written once.
trait Cell: Copy {
    const WORDS: usize;
    fn init(seed: u32, index: u64) -> Self;
    fn zero() -> Self;
    fn words(self) -> [u32; 4];
    /// `self += weight * value`.
    fn add_scaled(&mut self, weight: F, value: Self);
}

impl Cell for F {
    const WORDS: usize = CLASS_WORDS[CLASS_BF];
    fn init(seed: u32, index: u64) -> Self {
        init_bf(seed, index)
    }
    fn zero() -> Self {
        F::ZERO
    }
    fn words(self) -> [u32; 4] {
        [self.raw_u32_value(), 0, 0, 0]
    }
    fn add_scaled(&mut self, weight: F, value: Self) {
        self.add_assign_product(&weight, &value);
    }
}

impl Cell for E4 {
    const WORDS: usize = CLASS_WORDS[CLASS_E4];
    fn init(seed: u32, index: u64) -> Self {
        init_e4(seed, index)
    }
    fn zero() -> Self {
        E4::ZERO
    }
    fn words(self) -> [u32; 4] {
        e4_words(self)
    }
    fn add_scaled(&mut self, weight: F, value: Self) {
        <E4 as FieldExtension<F>>::add_assign_product_with_base(self, &value, &weight);
    }
}

/// Taps of one column, indexed `tap * rows + row`, addressed through
/// [`source_offset`] — the host mirror of the device accessor — so a disagreement
/// between the accessor and the LDE kernel's own address arithmetic shows up here.
fn column_taps<T: Cell>(
    layout: &Layout,
    seed: u32,
    window: usize,
    rec: UniskipSourceRecord,
) -> Vec<T> {
    let base = layout.windows[window].offset;
    let mut out = Vec::with_capacity(layout.column_elements() as usize);
    for tap in 0..UNISKIP_TAPS {
        for row in 0..layout.rows {
            let (buffer, offset) = source_offset(rec, cell_for_tap(tap), row, layout.log_rows);
            assert_eq!(buffer, CellBuffer::Tap);
            out.push(T::init(seed, base + offset));
        }
    }
    out
}

fn block_words<T: Cell>(layout: &Layout, values: &[T], positions: &[u64]) -> Vec<u32> {
    let mut out = vec![0u32; layout.column_elements() as usize * T::WORDS];
    for (value, &position) in values.iter().zip(positions) {
        let start = position as usize * T::WORDS;
        out[start..start + T::WORDS].copy_from_slice(&value.words()[..T::WORDS]);
    }
    out
}

/// Positions of a column's cells inside its downloaded block, taken from
/// [`source_offset`] rather than assumed: `cells` are device cell ids in the same
/// order the values were built.
fn block_positions(
    layout: &Layout,
    rec: UniskipSourceRecord,
    cells: impl Iterator<Item = usize> + Clone,
    buffer: CellBuffer,
) -> Vec<u64> {
    let column_start = addr_column(rec.addr) as u64 * layout.column_elements();
    let mut out = Vec::with_capacity(layout.column_elements() as usize);
    for cell in cells {
        for row in 0..layout.rows {
            let (got, offset) = source_offset(rec, cell, row, layout.log_rows);
            assert_eq!(got, buffer);
            out.push(offset - column_start);
        }
    }
    out
}

fn expected_words<T: Cell>(
    layout: &Layout,
    seed: u32,
    window: usize,
    rec: UniskipSourceRecord,
) -> (Vec<u32>, Vec<u32>) {
    let taps = column_taps::<T>(layout, seed, window, rec);
    let tap_positions = block_positions(
        layout,
        rec,
        (0..UNISKIP_TAPS).map(cell_for_tap),
        CellBuffer::Tap,
    );

    let matrix = lde_matrix();
    let mut coset = Vec::with_capacity(layout.column_elements() as usize);
    for weights in &matrix {
        for row in 0..layout.rows as usize {
            let mut acc = T::zero();
            for (t, weight) in weights.iter().enumerate() {
                acc.add_scaled(*weight, taps[t * layout.rows as usize + row]);
            }
            coset.push(acc);
        }
    }
    let coset_positions = block_positions(
        layout,
        rec,
        (0..UNISKIP_TAPS).map(cell_for_coset_row),
        CellBuffer::Coset,
    );

    (
        block_words(layout, &taps, &tap_positions),
        block_words(layout, &coset, &coset_positions),
    )
}

/// Expected device words of one column's tap block and coset block.
pub fn expected_column_words(
    layout: &Layout,
    seed: u32,
    window: usize,
    rec: UniskipSourceRecord,
) -> (Vec<u32>, Vec<u32>) {
    match class_index(rec.source_class) {
        CLASS_BF => expected_words::<F>(layout, seed, window, rec),
        _ => expected_words::<E4>(layout, seed, window, rec),
    }
}

fn diff_block(
    label: &str,
    kind: &str,
    expected: &[u32],
    actual: &[u32],
    rows: u64,
    words: usize,
) -> Result<(), String> {
    if expected.len() != actual.len() {
        return Err(format!(
            "{label} {kind}: expected {} words, downloaded {}",
            expected.len(),
            actual.len()
        ));
    }
    for (i, (e, a)) in expected.iter().zip(actual).enumerate() {
        if e != a {
            let element = (i / words) as u64;
            return Err(format!(
                "{label} {kind}: plane {} row {} limb {}: expected {e:#010x}, got {a:#010x}",
                element / rows,
                element % rows,
                i % words
            ));
        }
    }
    Ok(())
}

/// Bit-exact check of one column's taps and all 16 coset cells.
pub fn check_column(
    layout: &Layout,
    seed: u32,
    window: usize,
    rec: UniskipSourceRecord,
    taps: &[u32],
    coset: &[u32],
    label: &str,
) -> Result<(), String> {
    let words = CLASS_WORDS[class_index(rec.source_class)];
    let (expected_taps, expected_coset) = expected_column_words(layout, seed, window, rec);
    diff_block(label, "taps", &expected_taps, taps, layout.rows, words)?;
    diff_block(label, "coset", &expected_coset, coset, layout.rows, words)
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::geometry::Geometry;
    use crate::synth::{generate, Census, SYNTH_E4_WINDOW};

    #[test]
    fn cpu_init_generator() {
        for seed in [0u32, 1, 7, u32::MAX] {
            for index in [0u64, 1, 17, 1 << 32, (1u64 << 32) + 5] {
                for component in 0..4u32 {
                    let canonical = init_canonical(seed, index, component);
                    assert!((1..F::ORDER).contains(&canonical), "{canonical}");
                    // The device repr is the Montgomery lift, and it round-trips.
                    assert_eq!(F::new(canonical).to_u32(), canonical);
                    assert_eq!(to_device_bf(canonical), F::new(canonical).raw_u32_value());
                }
            }
        }
        // Component tagging separates the four limbs of an e4.
        let x = init_e4(3, 9);
        let words = e4_words(x);
        assert_eq!(words.len(), 4);
        assert!(words.iter().all(|&w| w != 0));
        assert_eq!(words[0], init_bf(3, 9).raw_u32_value());
        for c in 1..4u32 {
            assert_ne!(init_canonical(3, 9, 0), init_canonical(3, 9, c));
        }
        // Distinct backing indices give distinct data — the reason the layout packs
        // windows into one backing instead of allocating each separately.
        assert_ne!(init_canonical(3, 9, 0), init_canonical(3, 10, 0));
    }

    #[test]
    fn cpu_tap_block_is_the_contiguous_init_sequence() {
        let geometry = Geometry::new(10).unwrap();
        let program = generate(5, Census::default()).unwrap();
        let layout = Layout::new(&program, &geometry);
        let seed = 5;

        for window in [0usize, SYNTH_E4_WINDOW] {
            let columns = layout.windows[window].columns as usize;
            for column in [0, columns - 1] {
                let rec = program
                    .sources
                    .iter()
                    .copied()
                    .find(|r| addr_window(r.addr) == window && addr_column(r.addr) == column)
                    .unwrap();
                let class = class_index(rec.source_class);
                let words = CLASS_WORDS[class];
                let (taps, _) = expected_column_words(&layout, seed, window, rec);

                // The accessor-driven placement must reproduce the flat backing the
                // download sees: element `i` of the block is init index
                // `column_base + i`.
                let base = layout.column_base(window, column);
                let mut flat = Vec::with_capacity(taps.len());
                for i in 0..layout.column_elements() {
                    let value = match class {
                        CLASS_BF => init_bf(seed, base + i).words(),
                        _ => init_e4(seed, base + i).words(),
                    };
                    flat.extend_from_slice(&value[..words]);
                }
                assert_eq!(taps, flat, "window {window} column {column}");
            }
        }
    }

    #[test]
    fn cpu_coset_block_extends_the_taps() {
        let geometry = Geometry::new(10).unwrap();
        let program = generate(5, Census::default()).unwrap();
        let layout = Layout::new(&program, &geometry);
        let matrix = lde_matrix();
        let rec = program.sources[0];
        let (_, coset) = expected_column_words(&layout, 5, 0, rec);

        let base = layout.column_base(0, addr_column(rec.addr));
        let rows = layout.rows;
        for (c, weights) in matrix.iter().enumerate() {
            for row in [0u64, rows / 2, rows - 1] {
                let mut want = F::ZERO;
                for (t, weight) in weights.iter().enumerate() {
                    let tap = init_bf(5, base + (t as u64) * rows + row);
                    want.add_assign_product(weight, &tap);
                }
                let index = (c as u64 * rows + row) as usize;
                assert_eq!(
                    coset[index],
                    want.raw_u32_value(),
                    "cell {} row {row}",
                    cell_for_coset_row(c)
                );
            }
        }
    }
}
