//! Lossless JSON export of materialized setup, independent of witness generation.
//!
//! Columns include the complete committed domain, including unsupported decoder
//! entries and padding. Affine blocks are data compression, not table recipes.

use super::setup::GKRSetup;
use crate::gkr::virtual_polys::range_check::materialize_virtual_range_check_setup_poly;
use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::tables::{LookupWrapper, TableDriver};
use field::{PrimeField, TwoAdicField};
use serde::{Deserialize, Serialize};
use std::alloc::Global;
use std::io::Write;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ColumnBlock {
    Affine {
        length: usize,
        first: u32,
        step: i64,
    },
    Dense {
        values: Vec<u32>,
    },
    Periodic {
        repetitions: usize,
        stride: i64,
        values: Vec<u32>,
    },
}

impl ColumnBlock {
    pub fn len(&self) -> usize {
        match self {
            Self::Affine { length, .. } => *length,
            Self::Dense { values } => values.len(),
            Self::Periodic {
                repetitions,
                values,
                ..
            } => repetitions.saturating_mul(values.len()),
        }
    }

    pub fn value_at(&self, index: usize) -> Option<u32> {
        if index >= self.len() {
            return None;
        }
        match self {
            Self::Affine { first, step, .. } => {
                let offset = step.checked_mul(i64::try_from(index).ok()?)?;
                u32::try_from(i64::from(*first).checked_add(offset)?).ok()
            }
            Self::Dense { values } => values.get(index).copied(),
            Self::Periodic { stride, values, .. } => {
                let offset = stride.checked_mul(i64::try_from(index / values.len()).ok()?)?;
                u32::try_from(i64::from(values[index % values.len()]).checked_add(offset)?).ok()
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EncodedColumn {
    pub blocks: Vec<ColumnBlock>,
}

impl EncodedColumn {
    /// Compress only runs observed in the actual materialized column.
    pub fn encode(length: usize, value: impl Fn(usize) -> u32) -> Self {
        let mut blocks = Vec::new();
        let mut dense = Vec::new();
        let mut index = 0;
        while index < length {
            let first = value(index);
            let step = if index + 1 < length {
                i64::from(value(index + 1)) - i64::from(first)
            } else {
                0
            };
            let mut end = index + 1;
            while end < length && i64::from(value(end)) - i64::from(value(end - 1)) == step {
                end += 1;
            }
            let mut periodic = None;
            if end - index < 4096 {
                for period in [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024] {
                    if index + 4 * period > length {
                        break;
                    }
                    let stride = i64::from(value(index + period)) - i64::from(first);
                    if (1..4).any(|copy| {
                        i64::from(value(index + copy * period))
                            != i64::from(first) + stride * copy as i64
                    }) {
                        continue;
                    }
                    let mut copies = 1;
                    while index + (copies + 1) * period <= length {
                        if (0..period).any(|i| {
                            i64::from(value(index + copies * period + i))
                                != i64::from(value(index + i)) + stride * copies as i64
                        }) {
                            break;
                        }
                        copies += 1;
                    }
                    if copies >= 4 && copies * period > end - index {
                        if periodic
                            .as_ref()
                            .is_none_or(|block: &ColumnBlock| block.len() < copies * period)
                        {
                            periodic = Some(ColumnBlock::Periodic {
                                repetitions: copies,
                                stride,
                                values: (0..period).map(|i| value(index + i)).collect(),
                            });
                        }
                    }
                }
            }
            if let Some(block) = periodic {
                if !dense.is_empty() {
                    blocks.push(ColumnBlock::Dense {
                        values: std::mem::take(&mut dense),
                    });
                }
                index += block.len();
                blocks.push(block);
            } else if end - index >= 4 {
                if !dense.is_empty() {
                    blocks.push(ColumnBlock::Dense {
                        values: std::mem::take(&mut dense),
                    });
                }
                blocks.push(ColumnBlock::Affine {
                    length: end - index,
                    first,
                    step,
                });
                index = end;
            } else {
                dense.push(first);
                index += 1;
                if dense.len() == 4096 {
                    blocks.push(ColumnBlock::Dense {
                        values: std::mem::take(&mut dense),
                    });
                }
            }
        }
        if !dense.is_empty() {
            blocks.push(ColumnBlock::Dense { values: dense });
        }
        Self { blocks }
    }

    pub fn value_at(&self, mut index: usize) -> Option<u32> {
        for block in &self.blocks {
            if index < block.len() {
                return block.value_at(index);
            }
            index -= block.len();
        }
        None
    }

    pub fn matches_values(&self, length: usize, value: impl Fn(usize) -> u32) -> bool {
        let mut row = 0;
        for block in &self.blocks {
            for index in 0..block.len() {
                if row >= length || block.value_at(index) != Some(value(row)) {
                    return false;
                }
                row += 1;
            }
        }
        row == length
    }

    pub fn validate(&self, length: usize, exclusive_bound: u64) -> Result<(), String> {
        let mut covered = 0usize;
        for block in &self.blocks {
            if block.len() == 0 {
                return Err("empty setup column block".into());
            }
            covered = covered
                .checked_add(block.len())
                .ok_or("column length overflow")?;
            if covered > length {
                return Err("setup column exceeds its domain".into());
            }
            match block {
                ColumnBlock::Affine { .. } => {
                    for index in [0, block.len() - 1] {
                        let value = block.value_at(index).ok_or("affine column overflow")?;
                        if u64::from(value) >= exclusive_bound {
                            return Err("noncanonical setup field element".into());
                        }
                    }
                }
                ColumnBlock::Dense { values } => {
                    if values
                        .iter()
                        .any(|value| u64::from(*value) >= exclusive_bound)
                    {
                        return Err("noncanonical setup field element".into());
                    }
                }
                ColumnBlock::Periodic {
                    repetitions,
                    stride,
                    values,
                } => {
                    let offset = stride
                        .checked_mul(
                            i64::try_from(repetitions - 1)
                                .map_err(|_| "periodic column overflow")?,
                        )
                        .ok_or("periodic column overflow")?;
                    for first in values {
                        let last = i64::from(*first)
                            .checked_add(offset)
                            .and_then(|value| u32::try_from(value).ok())
                            .ok_or("periodic column overflow")?;
                        if u64::from(*first) >= exclusive_bound
                            || u64::from(last) >= exclusive_bound
                        {
                            return Err("noncanonical setup field element".into());
                        }
                    }
                }
            }
        }
        if covered != length {
            return Err("setup column does not cover its domain".into());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TableRegion {
    pub id: u32,
    pub offset: usize,
    pub length: usize,
    pub width: usize,
    pub key_columns: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SetupProgram {
    pub image_words: usize,
    pub image: EncodedColumn,
    pub text_words: usize,
    pub text: EncodedColumn,
}

impl SetupProgram {
    /// Inputs are exactly the image/text slices supplied to setup, including padding.
    pub fn new(image: &[u32], text: &[u32]) -> Self {
        Self {
            image_words: image.len(),
            image: EncodedColumn::encode(image.len(), |i| image[i]),
            text_words: text.len(),
            text: EncodedColumn::encode(text.len(), |i| text[i]),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SetupArtifact {
    pub version: u32,
    pub field_modulus: u32,
    pub trace_len: usize,
    /// The actual circuit object used by this setup, not a layout name.
    pub circuit: serde_json::Value,
    pub program: Option<SetupProgram>,
    pub tables: Vec<TableRegion>,
    pub columns: Vec<EncodedColumn>,
    pub range16: EncodedColumn,
    pub timestamp_range: EncodedColumn,
}

impl<F: PrimeField + TwoAdicField + Serialize> GKRSetup<F> {
    /// Export after construction and before commitment. The caller supplies the
    /// same circuit, table driver and program inputs used to construct this setup.
    pub fn artifact(
        &self,
        circuit: &GKRCircuitArtifact<F>,
        table_driver: &TableDriver<F>,
        program: Option<SetupProgram>,
    ) -> Result<SetupArtifact, String> {
        let field_modulus = u32::try_from(F::CHARACTERISTICS_U128)
            .map_err(|_| "setup JSON currently supports fields of at most 32 bits")?;
        if !circuit.trace_len.is_power_of_two()
            || circuit.trace_len < (1 << TIMESTAMP_COLUMNS_NUM_BITS)
        {
            return Err("setup domain is too small for its virtual range tables".into());
        }
        if self.hypercube_evals.len() != circuit.generic_lookup_tables_width
            || self
                .hypercube_evals
                .iter()
                .any(|column| column.len() != circuit.trace_len)
        {
            return Err("materialized setup shape differs from circuit".into());
        }
        let mut tables = Vec::new();
        for table in &table_driver.tables {
            if let LookupWrapper::Initialized(table) = table {
                tables.push(TableRegion {
                    id: table.id,
                    offset: table_driver.get_start_table_offset(table.id),
                    length: table.table_size(),
                    width: table.width(),
                    key_columns: table.num_keys(),
                });
            }
        }
        let columns: Vec<EncodedColumn> = self
            .hypercube_evals
            .iter()
            .map(|column| EncodedColumn::encode(column.len(), |i| column[i].as_u32_reduced()))
            .collect();
        for (encoded, actual) in columns.iter().zip(&self.hypercube_evals) {
            if !encoded.matches_values(actual.len(), |i| actual[i].as_u32_reduced()) {
                return Err("compressed setup column differs from materialized data".into());
            }
        }
        let range16 = materialize_virtual_range_check_setup_poly::<F, Global, 16>(
            circuit.trace_len.trailing_zeros(),
        );
        let range16 = EncodedColumn::encode(range16.len(), |i| range16[i].as_u32_reduced());
        let timestamp_range =
            materialize_virtual_range_check_setup_poly::<F, Global, TIMESTAMP_COLUMNS_NUM_BITS>(
                circuit.trace_len.trailing_zeros(),
            );
        let timestamp_range = EncodedColumn::encode(timestamp_range.len(), |i| {
            timestamp_range[i].as_u32_reduced()
        });
        let artifact = SetupArtifact {
            version: 1,
            field_modulus,
            trace_len: circuit.trace_len,
            circuit: serde_json::to_value(circuit).map_err(|error| error.to_string())?,
            program,
            tables,
            columns,
            range16,
            timestamp_range,
        };
        artifact.validate()?;
        Ok(artifact)
    }

    pub fn write_artifact_json(
        &self,
        writer: impl Write,
        circuit: &GKRCircuitArtifact<F>,
        table_driver: &TableDriver<F>,
        program: Option<SetupProgram>,
    ) -> Result<(), String> {
        let artifact = self.artifact(circuit, table_driver, program)?;
        serde_json::to_writer(writer, &artifact).map_err(|error| error.to_string())
    }
}

impl SetupArtifact {
    pub fn validate(&self) -> Result<(), String> {
        if self.version != 1 || self.field_modulus < 2 || !self.trace_len.is_power_of_two() {
            return Err("unsupported setup JSON header".into());
        }
        let circuit_trace = self.circuit["trace_len"].as_u64();
        let circuit_width = self.circuit["generic_lookup_tables_width"].as_u64();
        if circuit_trace != Some(self.trace_len as u64)
            || circuit_width != Some(self.columns.len() as u64)
        {
            return Err("setup JSON and circuit shapes differ".into());
        }
        for column in &self.columns {
            column.validate(self.trace_len, u64::from(self.field_modulus))?;
        }
        self.range16
            .validate(self.trace_len, u64::from(self.field_modulus))?;
        self.timestamp_range
            .validate(self.trace_len, u64::from(self.field_modulus))?;
        if let Some(program) = &self.program {
            program.image.validate(program.image_words, 1u64 << 32)?;
            program.text.validate(program.text_words, 1u64 << 32)?;
        }
        let mut end = 0usize;
        let mut previous_id = None;
        for table in &self.tables {
            if previous_id.is_some_and(|id| id >= table.id)
                || table.offset != end
                || table.length == 0
                || table.key_columns > table.width
                || table.width >= self.columns.len()
            {
                return Err("invalid setup table region".into());
            }
            let offset = self.circuit["table_offsets"]
                .get(table.id as usize)
                .and_then(serde_json::Value::as_u64);
            if offset != Some(table.offset as u64) {
                return Err("setup table offset differs from circuit".into());
            }
            end = end
                .checked_add(table.length)
                .ok_or("table region overflow")?;
            previous_id = Some(table.id);
        }
        if self.circuit["offset_for_decoder_table"].as_u64() != Some(end as u64) {
            return Err("decoder offset differs from materialized tables".into());
        }
        let total = self.circuit["total_tables_size"]
            .as_u64()
            .ok_or("missing table size")?;
        if total < end as u64 || total > self.trace_len as u64 {
            return Err("invalid decoder/setup extent".into());
        }
        let has_decoder = self.circuit["has_decoder_lookup"]
            .as_bool()
            .ok_or("missing decoder profile")?;
        if has_decoder && self.program.is_none() {
            return Err("decoder setup export requires its selected program inputs".into());
        }
        if !has_decoder && total != end as u64 {
            return Err("non-decoder setup has unaccounted real rows".into());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lossless_columns_cover_repeated_strides_dense_words_and_overflows() {
        let mut values = vec![u32::MAX; 17];
        for repeat in 0..60 {
            values.extend([50000, 100000, 77, 500].map(|first| first - repeat));
        }
        let mut state = 19u32;
        for _ in 0..2049 {
            state = state.wrapping_mul(1664525).wrapping_add(1013904223);
            values.push(state);
        }
        values.extend((0..8192).map(|i| i % 1024));
        let encoded = EncodedColumn::encode(values.len(), |i| values[i]);
        encoded.validate(values.len(), 1u64 << 32).unwrap();
        assert!(encoded.matches_values(values.len(), |i| values[i]));
        assert!(encoded
            .blocks
            .iter()
            .any(|block| matches!(block, ColumnBlock::Periodic { stride, .. } if *stride < 0)));
        assert!(encoded
            .blocks
            .iter()
            .any(|block| matches!(block, ColumnBlock::Dense { .. })));
        let source = serde_json::to_string(&encoded).unwrap();
        let parsed: EncodedColumn = serde_json::from_str(&source).unwrap();
        assert_eq!(parsed, encoded);
        assert!(parsed.matches_values(values.len(), |i| values[i]));
        assert!(EncodedColumn {
            blocks: vec![ColumnBlock::Periodic {
                repetitions: usize::MAX,
                stride: 0,
                values: vec![0, 1],
            }]
        }
        .validate(16, 1u64 << 32)
        .is_err());
        assert!(EncodedColumn {
            blocks: vec![ColumnBlock::Periodic {
                repetitions: 4,
                stride: -1,
                values: vec![0],
            }]
        }
        .validate(4, 1u64 << 32)
        .is_err());
        assert!(serde_json::from_str::<EncodedColumn>(
            r#"{"blocks":[{"kind":"recipe","formula":"xor"}]}"#
        )
        .is_err());
    }
}
