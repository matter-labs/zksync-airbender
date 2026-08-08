//! Host reference for the device init generator and the coset LDE.
//!
//! Bit-exactness, not just algebraic agreement: every value here is compared
//! against the device word for word, so the canonical -> Montgomery conversion
//! must be the one `bf::from_u32_unchecked` performs on the device.

use field::{Field, FieldExtension};

use crate::abi::*;
use crate::domain::{fold_weights, lde_matrix, ntt_twiddles, E4, F};
use crate::geometry::{Geometry, UNISKIP_MAX_LOG_ROWS};
use crate::harness::{class_index, Layout, CLASS_BF, CLASS_E4, CLASS_WORDS};
use crate::synth::SynthProgram;

/// DERIVED-TABLE INIT SPACE. The generator keys on the absolute element index inside
/// an allocation, so two tables that both start at index 0 would hold identical data
/// and an index confusion between them would be invisible. The three derived `e4`
/// tables therefore share one virtual index space — eq high (both tables), then the
/// coefficient bank, then eq low. `eq_low`'s device allocation carries the prefix as
/// an unused pad so its slice genuinely starts at [`UNISKIP_EQ_LOW_INIT_BASE`].
pub const UNISKIP_EQ_HIGH_INIT_BASE: u64 = 0;
pub const UNISKIP_COEFF_INIT_BASE: u64 = UNISKIP_EQ_HIGH_INIT_BASE + 2 * UNISKIP_EQ_HIGH as u64;
pub const UNISKIP_EQ_LOW_INIT_BASE: u64 = UNISKIP_COEFF_INIT_BASE + UNISKIP_COEFF_BANK as u64;
/// Entries eq low can occupy at the largest addressable geometry — the high tables
/// fill first, so its bit count is `UNISKIP_MAX_LOG_ROWS - 2 * UNISKIP_LOG_EQ_HIGH`.
/// The challenge sits past that, so its draws stay distinct at every `log_rows`.
pub const UNISKIP_EQ_LOW_INIT_MAX_LEN: u64 = 1 << (UNISKIP_MAX_LOG_ROWS - 2 * UNISKIP_LOG_EQ_HIGH);
pub const UNISKIP_CHALLENGE_INIT_BASE: u64 = UNISKIP_EQ_LOW_INIT_BASE + UNISKIP_EQ_LOW_INIT_MAX_LEN;

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

/// The LSB producer's lane-indexed twiddles, flattened `[table * UNISKIP_TAPS + lane]`
/// — the order the device hoists into its per-lane register file. See
/// [`crate::domain::ntt_twiddles`] for the stage order.
pub fn ntt_twiddle_words() -> [u32; UNISKIP_NTT_TABLES * UNISKIP_TAPS] {
    let tables = ntt_twiddles();
    core::array::from_fn(|i| tables[i / UNISKIP_TAPS][i % UNISKIP_TAPS].raw_u32_value())
}

/// Entry `index` of the eq high symbol: `[0, UNISKIP_EQ_HIGH)` is table 0, the
/// remainder table 1.
fn eq_high_value(seed: u32, index: usize) -> E4 {
    init_e4(seed, UNISKIP_EQ_HIGH_INIT_BASE + index as u64)
}

fn eq_low_value(seed: u32, index: usize) -> E4 {
    init_e4(seed, UNISKIP_EQ_LOW_INIT_BASE + index as u64)
}

/// Both eq high tables as one allocation of `2 * UNISKIP_EQ_HIGH` `e4` entries:
/// table 0 first, table 1 from `UNISKIP_EQ_HIGH`. Synthetic weights — they carry
/// the production factored shape, not a transcript-real `q`. `flat_eq` forces the
/// whole symbol to ONE, the `--validate-flat-eq` debug mode.
pub fn eq_high_words(seed: u32, flat_eq: bool) -> [[u32; 4]; 2 * UNISKIP_EQ_HIGH] {
    core::array::from_fn(|i| {
        e4_words(if flat_eq {
            E4::ONE
        } else {
            eq_high_value(seed, i)
        })
    })
}

/// The `e4` the `--validate-flat-eq` mode writes over every eq entry.
pub fn e4_one_words() -> [u32; 4] {
    e4_words(E4::ONE)
}

/// The coefficient bank the eval kernel indexes by `term.coeff`.
pub fn coeff_bank(seed: u32) -> [E4; UNISKIP_COEFF_BANK] {
    core::array::from_fn(|i| init_e4(seed, UNISKIP_COEFF_INIT_BASE + i as u64))
}

pub fn coeff_bank_words(seed: u32) -> [[u32; 4]; UNISKIP_COEFF_BANK] {
    coeff_bank(seed).map(e4_words)
}

fn e4_words(x: E4) -> [u32; 4] {
    [x.c0.c0, x.c0.c1, x.c1.c0, x.c1.c1].map(|f| f.raw_u32_value())
}

/// The round challenge `r`: four init draws, one per `E4` coordinate. Synthetic —
/// the bench has no transcript, so `r` is a deterministic function of `--seed`
/// rather than a Fiat-Shamir squeeze.
pub fn fold_challenge(seed: u32) -> E4 {
    E4::from_array_of_base(core::array::from_fn(|j| {
        F::new(init_canonical(
            seed,
            UNISKIP_CHALLENGE_INIT_BASE + j as u64,
            0,
        ))
    }))
}

/// `[L_t(r)]_t` in tap order, as the device words the fold kernels index.
pub fn fold_weight_words(seed: u32) -> [[u32; 4]; UNISKIP_TAPS] {
    fold_weights(fold_challenge(seed)).map(e4_words)
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
    /// `acc += weight * self` — the fold's `E4`-weighted accumulation.
    fn add_to_e4(self, weight: E4, acc: &mut E4);
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
    fn add_to_e4(self, weight: E4, acc: &mut E4) {
        acc.add_assign_product_with_base(&weight, &self);
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
    fn add_to_e4(self, weight: E4, acc: &mut E4) {
        acc.add_assign_product(&weight, &self);
    }
}

/// Taps of one column, indexed `tap * rows + row`, addressed through
/// [`Layout::source_offset`] — the host mirror of the device accessor — so a disagreement
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
            let (buffer, offset) = layout.source_offset(rec, cell_for_tap(tap), row);
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
/// [`Layout::source_offset`] rather than assumed: `cells` are device cell ids in the same
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
            let (got, offset) = layout.source_offset(rec, cell, row);
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

/// All 32 cells of one source at one row: the 16 taps straight from the init
/// generator, the 16 coset cells extended by the same LDE the device runs. The
/// oracle recomputes them instead of reading the device coset buffer.
fn source_cells<T: Cell>(
    layout: &Layout,
    matrix: &[[F; UNISKIP_TAPS]; UNISKIP_TAPS],
    seed: u32,
    window: usize,
    rec: UniskipSourceRecord,
    row: u64,
    out: &mut [T; UNISKIP_CELLS],
) {
    let base = layout.windows[window].offset;
    for tap in 0..UNISKIP_TAPS {
        let (buffer, offset) = layout.source_offset(rec, cell_for_tap(tap), row);
        debug_assert_eq!(buffer, CellBuffer::Tap);
        out[cell_for_tap(tap)] = T::init(seed, base + offset);
    }
    for (c, weights) in matrix.iter().enumerate() {
        let mut acc = T::zero();
        for (t, weight) in weights.iter().enumerate() {
            acc.add_scaled(*weight, out[cell_for_tap(t)]);
        }
        out[cell_for_coset_row(c)] = acc;
    }
}

/// Every source's 32 cell values at one row, reused across rows.
struct RowValues {
    bf: Vec<[F; UNISKIP_CELLS]>,
    e4: Vec<[E4; UNISKIP_CELLS]>,
}

impl RowValues {
    fn new(sources: usize) -> Self {
        Self {
            bf: vec![[F::ZERO; UNISKIP_CELLS]; sources],
            e4: vec![[E4::ZERO; UNISKIP_CELLS]; sources],
        }
    }

    fn fill(
        &mut self,
        layout: &Layout,
        matrix: &[[F; UNISKIP_TAPS]; UNISKIP_TAPS],
        program: &SynthProgram,
        seed: u32,
        row: u64,
    ) {
        for (id, rec) in program.sources.iter().enumerate() {
            let window = addr_window(rec.addr);
            match class_index(rec.source_class) {
                CLASS_BF => source_cells(layout, matrix, seed, window, *rec, row, &mut self.bf[id]),
                _ => source_cells(layout, matrix, seed, window, *rec, row, &mut self.e4[id]),
            }
        }
    }
}

/// `T(row)`: the factored eq weight, composed exactly as `uniskip_eq_at` does.
fn eq_at(geometry: &Geometry, seed: u32, row: u64, flat_eq: bool) -> E4 {
    if flat_eq {
        return E4::ONE;
    }
    let (high0, high1, low) = geometry.split_row(row);
    let mut eq = eq_high_value(seed, high0);
    eq.mul_assign(&eq_high_value(seed, UNISKIP_EQ_HIGH + high1));
    eq.mul_assign(&eq_low_value(seed, low));
    eq
}

/// One row's contribution to each cell, before the eq weight: the same record walk
/// the eval kernel runs, over all 32 cells instead of a warp's 4.
fn run_program(
    program: &SynthProgram,
    values: &RowValues,
    coeffs: &[E4; UNISKIP_COEFF_BANK],
    immediates: &[F; UNISKIP_MAX_IMMEDIATES],
    acc: &mut [E4; UNISKIP_CELLS],
) {
    let mut pc = 0usize;
    while pc < program.program.len() {
        let term = program.program[pc];
        let coeff = coeffs[term.coeff as usize];
        if term.term_class == UNISKIP_CLASS_GROUP_BF {
            let arity = term.source_a as usize;
            let mut sum = [F::ZERO; UNISKIP_CELLS];
            for m in 1..=arity {
                let member = program.program[pc + m];
                let a = &values.bf[member.source_a as usize];
                for (cell, sum) in sum.iter_mut().enumerate() {
                    let mut value = a[cell];
                    if member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF {
                        value.mul_assign(&values.bf[member.source_b as usize][cell]);
                    }
                    match member.coeff {
                        UNISKIP_IMMEDIATE_ONE => sum.add_assign(&value),
                        UNISKIP_IMMEDIATE_NEG_ONE => sum.sub_assign(&value),
                        id => sum.add_assign_product(
                            &immediates[(id - UNISKIP_IMMEDIATE_RESERVED) as usize],
                            &value,
                        ),
                    };
                }
            }
            for (cell, acc) in acc.iter_mut().enumerate() {
                acc.add_assign_product_with_base(&coeff, &sum[cell]);
            }
            pc += arity + 1;
            continue;
        }
        let a = term.source_a as usize;
        let b = term.source_b as usize;
        for (cell, acc) in acc.iter_mut().enumerate() {
            match term.term_class {
                UNISKIP_CLASS_LINEAR_BF => {
                    acc.add_assign_product_with_base(&coeff, &values.bf[a][cell]);
                }
                UNISKIP_CLASS_LINEAR_E4 => {
                    acc.add_assign_product(&coeff, &values.e4[a][cell]);
                }
                UNISKIP_CLASS_PRODUCT_BF_BF => {
                    let mut value = values.bf[a][cell];
                    value.mul_assign(&values.bf[b][cell]);
                    acc.add_assign_product_with_base(&coeff, &value);
                }
                UNISKIP_CLASS_PRODUCT_BF_E4 => {
                    let mut value = values.e4[b][cell];
                    value.mul_assign_by_base(&values.bf[a][cell]);
                    acc.add_assign_product(&coeff, &value);
                }
                UNISKIP_CLASS_PRODUCT_E4_E4 => {
                    let mut value = values.e4[a][cell];
                    value.mul_assign(&values.e4[b][cell]);
                    acc.add_assign_product(&coeff, &value);
                }
                other => unreachable!("record {pc} has class {other}"),
            }
        }
        pc += 1;
    }
}

/// FULL ORACLE of the eval + finalize pass:
/// `q[cell] = Σ_row T(row) · Σ_terms coeff · value(cell, row)`.
///
/// Independent of the device by construction — it regenerates the operand data from
/// the init formula and re-extends it to the coset itself. Cost is
/// `O(rows · sources · UNISKIP_TAPS²)`, so it is a small-`--log-trace` validation
/// path, not something to run at the benchmark size.
pub fn eval_q(
    program: &SynthProgram,
    geometry: &Geometry,
    seed: u32,
    flat_eq: bool,
    source_layout: SourceLayout,
) -> [E4; UNISKIP_CELLS] {
    let layout = Layout::new(program, geometry, source_layout);
    let matrix = lde_matrix();
    let coeffs = coeff_bank(seed);
    let immediates = program.immediates_canonical.map(F::new);
    let mut values = RowValues::new(program.sources.len());
    let mut totals = [E4::ZERO; UNISKIP_CELLS];
    for row in 0..layout.rows {
        values.fill(&layout, &matrix, program, seed, row);
        let mut acc = [E4::ZERO; UNISKIP_CELLS];
        run_program(program, &values, &coeffs, &immediates, &mut acc);
        let eq = eq_at(geometry, seed, row, flat_eq);
        for (cell, total) in totals.iter_mut().enumerate() {
            let mut scaled = acc[cell];
            scaled.mul_assign(&eq);
            total.add_assign(&scaled);
        }
    }
    totals
}

/// Bit-exact check of the downloaded `q`, four `u32` limbs per cell.
pub fn check_q(expected: &[E4; UNISKIP_CELLS], actual: &[u32]) -> Result<(), String> {
    let words = CLASS_WORDS[CLASS_E4];
    if actual.len() != UNISKIP_CELLS * words {
        return Err(format!(
            "q: expected {} words, downloaded {}",
            UNISKIP_CELLS * words,
            actual.len()
        ));
    }
    for (cell, want) in expected.iter().enumerate() {
        for (limb, want) in e4_words(*want).iter().enumerate() {
            let got = actual[cell * words + limb];
            if got != *want {
                return Err(format!(
                    "q cell {cell} limb {limb}: expected {want:#010x}, got {got:#010x}"
                ));
            }
        }
    }
    Ok(())
}

/// One source's folded value at one row: the same weighted sum of the 16 taps on
/// `H` the fold kernel runs, over data regenerated from the init formula and
/// addressed through [`Layout::source_offset`].
fn folded_row<T: Cell>(
    layout: &Layout,
    seed: u32,
    rec: UniskipSourceRecord,
    weights: &[E4; UNISKIP_TAPS],
    row: u64,
) -> E4 {
    let base = layout.windows[addr_window(rec.addr)].offset;
    let mut acc = E4::ZERO;
    for (tap, weight) in weights.iter().enumerate() {
        let (buffer, offset) = layout.source_offset(rec, cell_for_tap(tap), row);
        assert_eq!(buffer, CellBuffer::Tap);
        T::init(seed, base + offset).add_to_e4(*weight, &mut acc);
    }
    acc
}

/// Bit-exact check of one source's folded values at `rows`; `actual` holds four
/// `u32` limbs per sampled row, in `rows` order. The window comes from `rec.addr`,
/// so there is no window/record pair that could disagree.
pub fn fold_check(
    layout: &Layout,
    seed: u32,
    rec: UniskipSourceRecord,
    rows: &[u64],
    actual: &[u32],
    label: &str,
) -> Result<(), String> {
    let words = CLASS_WORDS[CLASS_E4];
    if actual.len() != rows.len() * words {
        return Err(format!(
            "{label} fold: expected {} words, downloaded {}",
            rows.len() * words,
            actual.len()
        ));
    }
    let weights = fold_weights(fold_challenge(seed));
    for (i, &row) in rows.iter().enumerate() {
        let want = match class_index(rec.source_class) {
            CLASS_BF => folded_row::<F>(layout, seed, rec, &weights, row),
            _ => folded_row::<E4>(layout, seed, rec, &weights, row),
        };
        for (limb, want) in e4_words(want).iter().enumerate() {
            let got = actual[i * words + limb];
            if got != *want {
                return Err(format!(
                    "{label} fold: row {row} limb {limb}: expected {want:#010x}, got {got:#010x}"
                ));
            }
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
        let layout = Layout::new(&program, &geometry, SourceLayout::PlaneMajor);
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

    /// The census guarantees every immediate id is exercised; this proves the
    /// oracle actually applies each one, so a device-repr conversion bug in
    /// `desc.immediates` cannot pass `--validate` unnoticed.
    #[test]
    fn cpu_eval_q_uses_every_immediate() {
        let geometry = Geometry::new(9).unwrap();
        let program = generate(5, Census::default()).unwrap();
        let baseline = eval_q(&program, &geometry, 5, false, SourceLayout::PlaneMajor);
        for slot in 0..UNISKIP_MAX_IMMEDIATES {
            let mut perturbed = program.clone();
            let value = &mut perturbed.immediates_canonical[slot];
            *value = if *value == 1 { 2 } else { *value - 1 };
            assert_ne!(
                eval_q(&perturbed, &geometry, 5, false, SourceLayout::PlaneMajor),
                baseline,
                "immediate slot {slot} does not reach q"
            );
        }
    }

    /// Pins the fold oracle's accessor-driven addressing against the flat
    /// plane-order view of a column block, for both field classes.
    #[test]
    fn cpu_fold_check_matches_the_flat_column() {
        // The challenge draws sit past the largest eq low table, so no geometry can
        // make them alias it.
        let widest = Geometry::new(crate::geometry::UNISKIP_MAX_LOG_TRACE).unwrap();
        assert!(
            UNISKIP_EQ_LOW_INIT_BASE + widest.eq_low_len() as u64 <= UNISKIP_CHALLENGE_INIT_BASE
        );

        let geometry = Geometry::new(10).unwrap();
        let program = generate(5, Census::default()).unwrap();
        let layout = Layout::new(&program, &geometry, SourceLayout::PlaneMajor);
        let seed = 5;
        let weights = fold_weights(fold_challenge(seed));
        let rows = [0u64, 1, layout.rows / 2, layout.rows - 1];

        for window in [0usize, SYNTH_E4_WINDOW] {
            let column = layout.windows[window].columns as usize - 1;
            let rec = program
                .sources
                .iter()
                .copied()
                .find(|r| addr_window(r.addr) == window && addr_column(r.addr) == column)
                .unwrap();
            let class = class_index(rec.source_class);
            let base = layout.column_base(window, column);
            let mut words = Vec::new();
            for &row in &rows {
                let mut acc = E4::ZERO;
                for (tap, weight) in weights.iter().enumerate() {
                    // Flat view: the column block is tap-major, `tap * rows + row`.
                    let index = base + tap as u64 * layout.rows + row;
                    match class {
                        CLASS_BF => init_bf(seed, index).add_to_e4(*weight, &mut acc),
                        _ => init_e4(seed, index).add_to_e4(*weight, &mut acc),
                    }
                }
                words.extend_from_slice(&e4_words(acc));
            }
            fold_check(&layout, seed, rec, &rows, &words, "cpu").unwrap();

            words[0] ^= 1;
            assert!(fold_check(&layout, seed, rec, &rows, &words, "cpu").is_err());
        }
    }

    #[test]
    fn cpu_coset_block_extends_the_taps() {
        let geometry = Geometry::new(10).unwrap();
        let program = generate(5, Census::default()).unwrap();
        let layout = Layout::new(&program, &geometry, SourceLayout::PlaneMajor);
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
