// Copied unchanged column codec from pinned v3 setup_artifact.rs; see provenance.json.
use serde::{Deserialize, Serialize};

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
