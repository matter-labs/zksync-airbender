//! Launch geometry of one uniskip pass at k = 4.

use crate::abi::{UNISKIP_CELLS, UNISKIP_LOG_EQ_HIGH, UNISKIP_ROWS_PER_BLOCK, UNISKIP_TAPS};

/// `log_rows` below this leaves fewer rows than a block covers.
pub const UNISKIP_MIN_LOG_ROWS: u32 = 5;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Geometry {
    pub log_trace: u32,
    /// `log_trace - 4`: rows of the k = 4 logical trace.
    pub log_rows: u32,
    pub logical_rows: u64,
    /// Eval-kernel blocks, each covering `UNISKIP_ROWS_PER_BLOCK` rows.
    pub blocks: u32,
    /// Bit counts of the factored eq groups: `(high0, high1, low)`, summing to `log_rows`.
    pub eq_sizes: (u32, u32, u32),
    /// `e4` slots the eval kernel writes: `UNISKIP_CELLS` per block.
    pub partials: u64,
    /// `e4` slots the finalize kernel writes.
    pub final_cells: u32,
}

impl Geometry {
    pub fn new(log_trace: u32) -> Result<Self, String> {
        let log_rows = log_trace
            .checked_sub(UNISKIP_TAPS.trailing_zeros())
            .ok_or_else(|| {
                format!(
                    "--log-trace {log_trace} is below the k = 4 skip factor ({} taps)",
                    UNISKIP_TAPS
                )
            })?;
        if log_rows < UNISKIP_MIN_LOG_ROWS {
            return Err(format!(
                "--log-trace {log_trace} gives log_rows {log_rows}, below the minimum {UNISKIP_MIN_LOG_ROWS}"
            ));
        }
        // HIGH-FIRST fill: each high table caps at UNISKIP_EQ_HIGH entries, the
        // remainder goes to the (device-memory) low table.
        let high0 = log_rows.min(UNISKIP_LOG_EQ_HIGH);
        let high1 = (log_rows - high0).min(UNISKIP_LOG_EQ_HIGH);
        let low = log_rows - high0 - high1;

        let logical_rows = 1u64 << log_rows;
        let rows_per_block = UNISKIP_ROWS_PER_BLOCK as u64;
        let blocks = logical_rows.div_ceil(rows_per_block);
        let blocks = u32::try_from(blocks)
            .map_err(|_| format!("--log-trace {log_trace} needs {blocks} blocks"))?;

        Ok(Self {
            log_trace,
            log_rows,
            logical_rows,
            blocks,
            eq_sizes: (high0, high1, low),
            partials: UNISKIP_CELLS as u64 * blocks as u64,
            final_cells: UNISKIP_CELLS as u32,
        })
    }

    /// Entries of eq high table `table` (0 or 1).
    pub fn eq_high_len(&self, table: usize) -> usize {
        let bits = match table {
            0 => self.eq_sizes.0,
            1 => self.eq_sizes.1,
            _ => panic!("eq high table {table} does not exist"),
        };
        1usize << bits
    }

    /// Entries of the eq low table.
    pub fn eq_low_len(&self) -> usize {
        1usize << self.eq_sizes.2
    }

    /// Table indices `(high0, high1, low)` of `row` — the bit-group split the eval
    /// kernel and the oracle share: the low `low` bits index `eq_low`, the next
    /// `high1` bits index high table 1, the top bits index high table 0.
    pub fn split_row(&self, row: u64) -> (usize, usize, usize) {
        let (high0, high1, low) = self.eq_sizes;
        let low_index = row & ((1u64 << low) - 1);
        let high1_index = (row >> low) & ((1u64 << high1) - 1);
        let high0_index = (row >> (low + high1)) & ((1u64 << high0) - 1);
        (
            high0_index as usize,
            high1_index as usize,
            low_index as usize,
        )
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::abi::UNISKIP_EQ_HIGH;

    #[test]
    fn cpu_geometry_k4() {
        let g = Geometry::new(10).unwrap();
        assert_eq!(g.log_rows, 6);
        assert_eq!(g.logical_rows, 64);
        assert_eq!(g.blocks, 2);
        assert_eq!(g.eq_sizes, (6, 0, 0));
        assert_eq!(g.partials, 64);
        assert_eq!(g.final_cells, 32);
        assert_eq!(g.eq_high_len(0), 64);
        assert_eq!(g.eq_high_len(1), 1);
        assert_eq!(g.eq_low_len(), 1);
    }

    #[test]
    fn cpu_geometry_eq_bounds() {
        let g = Geometry::new(24).unwrap();
        assert_eq!(g.log_rows, 20);
        assert_eq!(g.eq_sizes, (8, 8, 4));
        assert!(Geometry::new(8).is_err());

        for log_trace in 9..=32 {
            let g = Geometry::new(log_trace).unwrap();
            let (high0, high1, low) = g.eq_sizes;
            assert_eq!(high0 + high1 + low, g.log_rows, "log_trace {log_trace}");
            assert!(g.eq_high_len(0) <= UNISKIP_EQ_HIGH);
            assert!(g.eq_high_len(1) <= UNISKIP_EQ_HIGH);
            assert_eq!(g.logical_rows, 1 << g.log_rows);
            assert_eq!(
                g.blocks as u64 * UNISKIP_ROWS_PER_BLOCK as u64,
                g.logical_rows
            );
            assert_eq!(g.partials, UNISKIP_CELLS as u64 * g.blocks as u64);

            // Every row splits into in-range table indices and recomposes exactly.
            let rows = [
                0u64,
                1,
                37 % g.logical_rows,
                g.logical_rows / 3,
                g.logical_rows - 1,
            ];
            for row in rows {
                let (hi0, hi1, lo) = g.split_row(row);
                assert!(hi0 < g.eq_high_len(0) && hi1 < g.eq_high_len(1) && lo < g.eq_low_len());
                let back = ((hi0 as u64) << (high1 + low)) | ((hi1 as u64) << low) | lo as u64;
                assert_eq!(back, row, "log_trace {log_trace} row {row}");
            }
        }
    }
}
