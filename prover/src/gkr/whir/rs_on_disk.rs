//! On-disk storage for base RS codewords (the `RSQueriable` side of a base/setup
//! commitment, mirroring the tree-side [`on_disk`](crate::merkle_trees::on_disk)).
//!
//! A single LDE coset serializes to a small header plus its columns concatenated
//! column-major as field-element bytes:
//!
//! ```text
//! [ header: magic(4) elem_bytes(4) num_columns(8) coset_size_log2(8) ]
//! [ column 0: 2^coset_size_log2 field elements ]
//! [ column 1: ... ]  ...
//! ```
//!
//! Each field element is written with the cheapest exact little-endian
//! representation (close to a byte cast): `as_u32_raw_repr` (4 bytes) for small
//! fields (`CHAR_BITS < 32`), and `as_u128_reduced` (16 bytes) for larger ones —
//! reconstructed with `from_raw_repr_with_reduction` / `from_u128_with_reduction`.
//!
//! A full [`MaterializedCosets`] writes one such file per coset, sharing a common
//! path prefix. [`OnDiskRsCodewords`] reads them back through memory-mapped files
//! ([`tiverse_mmap`]): reads are lazy and positioned — only the queried leaf
//! elements (or, for `main_domain_column`, the one coset-0 column) are touched, so
//! the full codeword never has to be loaded into RAM. Coset 0 is the main domain.

use super::offsets_vec_for_leaf_construction;
use super::{ColumnMajorBaseOracleForCoset, MaterializedCosets};
use crate::merkle_trees::{MainDomainColumn, RSQueriable};
use field::{PrimeField, TwoAdicField};
use mmap_io::MemoryMappedFile;
use std::borrow::Cow;
use std::fs::File;
use std::io::Write;
use std::marker::PhantomData;
use std::path::PathBuf;

/// Magic marker ("RSC2") identifying a coset RS-codeword file.
pub const RS_CODEWORD_MAGIC: u32 = u32::from_le_bytes(*b"RSC2");

/// Header size in bytes: magic(4) + elem_bytes(4) + num_columns(8) + coset_size_log2(8).
pub const RS_HEADER_BYTES: usize = 4 + 4 + 8 + 8;

/// File extension for a serialized coset RS-codeword file (RS CodeWord).
pub const RS_CODEWORD_FILE_EXT: &str = "rscw";

/// Serialized byte width of one field element: the raw `u32` repr (4 bytes) for
/// small fields (`CHAR_BITS < 32`), the reduced-`u128` form (16 bytes) otherwise.
#[inline]
pub fn field_serialized_bytes<F: PrimeField>() -> usize {
    if F::CHAR_BITS < 32 {
        4
    } else {
        16
    }
}

/// Append one field element's little-endian bytes to `buf` (cheapest exact repr).
#[inline]
fn push_field_le<F: PrimeField>(buf: &mut Vec<u8>, x: F) {
    if F::CHAR_BITS < 32 {
        buf.extend_from_slice(&x.as_u32_raw_repr().to_le_bytes());
    } else {
        buf.extend_from_slice(&x.as_u128_reduced().to_le_bytes());
    }
}

/// Reconstruct one field element from its little-endian bytes (inverse of
/// [`push_field_le`]).
#[inline]
fn read_field_le<F: PrimeField>(bytes: &[u8]) -> F {
    if F::CHAR_BITS < 32 {
        F::from_raw_repr_with_reduction(u32::from_le_bytes(bytes[..4].try_into().unwrap()))
    } else {
        F::from_u128_with_reduction(u128::from_le_bytes(bytes[..16].try_into().unwrap()))
    }
}

fn mmap_io_err(e: impl core::fmt::Debug) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::Other, format!("mmap-io: {e:?}"))
}

/// Serialize a coset's RS codewords straight from its column slices (header +
/// column-major field bytes) into `writer`. Each column is converted into a
/// contiguous byte buffer and written in one bulk `write_all` (efficient; close to
/// a byte cast). Used both by [`serialize_coset`] and by the memory-light
/// coset-by-coset setup serializer.
pub fn serialize_coset_columns<F, W>(
    writer: &mut W,
    coset_size_log2: usize,
    columns: &[&[F]],
) -> std::io::Result<()>
where
    F: PrimeField + TwoAdicField,
    W: Write,
{
    let num_columns = columns.len();
    let coset_len = 1usize << coset_size_log2;
    let elem_bytes = field_serialized_bytes::<F>();

    writer.write_all(&RS_CODEWORD_MAGIC.to_le_bytes())?;
    writer.write_all(&(elem_bytes as u32).to_le_bytes())?;
    writer.write_all(&(num_columns as u64).to_le_bytes())?;
    writer.write_all(&(coset_size_log2 as u64).to_le_bytes())?;

    let mut buf = Vec::with_capacity(coset_len * elem_bytes);
    for col in columns.iter() {
        assert_eq!(
            col.len(),
            coset_len,
            "coset column length must be 2^coset_size_log2"
        );
        buf.clear();
        for &x in col.iter() {
            push_field_le(&mut buf, x);
        }
        writer.write_all(&buf)?;
    }
    Ok(())
}

/// Serialize one coset's RS codewords (header + column-major field bytes) into
/// `writer`.
pub fn serialize_coset<F, W>(
    coset: &ColumnMajorBaseOracleForCoset<F>,
    writer: &mut W,
) -> std::io::Result<()>
where
    F: PrimeField + TwoAdicField,
    W: Write,
{
    let columns: Vec<&[F]> = coset
        .original_values_normal_order
        .iter()
        .map(|c| &c.column[..])
        .collect();
    serialize_coset_columns(writer, coset.coset_size_log2, &columns)
}

impl<F: PrimeField + TwoAdicField> ColumnMajorBaseOracleForCoset<F> {
    /// Serialize this coset's RS codewords into any [`std::io::Write`] sink (see the
    /// module docs for the format).
    pub fn serialize_to_disk<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        serialize_coset(self, writer)
    }
}

/// The on-disk file path for coset `i` under a shared prefix, e.g.
/// `"<prefix>.coset_0003.rscw"`.
pub fn coset_file_path(path_prefix: &str, coset_index: usize) -> PathBuf {
    PathBuf::from(format!(
        "{path_prefix}.coset_{coset_index:04}.{RS_CODEWORD_FILE_EXT}"
    ))
}

impl<F: PrimeField + TwoAdicField> MaterializedCosets<F> {
    /// Umbrella serializer: write each LDE coset to its own file under a shared
    /// `path_prefix` (`coset_file_path(prefix, i)`), returning the paths written in
    /// coset order.
    pub fn serialize_to_disk(&self, path_prefix: &str) -> std::io::Result<Vec<PathBuf>> {
        let mut paths = Vec::with_capacity(self.cosets.len());
        for (i, coset) in self.cosets.iter().enumerate() {
            let path = coset_file_path(path_prefix, i);
            let mut file = std::io::BufWriter::new(File::create(&path)?);
            serialize_coset(coset, &mut file)?;
            file.flush()?;
            paths.push(path);
        }
        Ok(paths)
    }
}

/// A [`RSQueriable`] backed by per-coset memory-mapped files ([`mmap_io`], as
/// written by [`MaterializedCosets::serialize_to_disk`]). Reads are lazy and
/// positioned via the OS page cache — only the queried leaf elements (or the one
/// coset-0 column for `main_domain_column`) are ever touched, so the full codeword
/// never has to reside in RAM. Coset 0 is the main evaluation domain.
pub struct OnDiskRsCodewords<F: PrimeField + TwoAdicField> {
    coset_maps: Vec<MemoryMappedFile>,
    num_columns: usize,
    coset_size_log2: usize,
    elem_bytes: usize,
    _marker: PhantomData<fn() -> F>,
}

impl<F: PrimeField + TwoAdicField> core::fmt::Debug for OnDiskRsCodewords<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("OnDiskRsCodewords")
            .field("num_cosets", &self.coset_maps.len())
            .field("num_columns", &self.num_columns)
            .field("coset_size_log2", &self.coset_size_log2)
            .finish()
    }
}

impl<F: PrimeField + TwoAdicField> OnDiskRsCodewords<F> {
    /// Memory-map a set of coset files (in coset order; coset 0 = main domain)
    /// previously written for this field, validating each file's header.
    pub fn open(coset_paths: Vec<PathBuf>) -> std::io::Result<Self> {
        assert!(!coset_paths.is_empty(), "need at least one coset file");
        let mut coset_maps: Vec<MemoryMappedFile> = Vec::with_capacity(coset_paths.len());
        let mut dims: Option<(usize, usize, usize)> = None;
        for path in coset_paths.iter() {
            let mmap = MemoryMappedFile::open_ro(path).map_err(mmap_io_err)?;
            let header = Self::parse_header(&mmap)?;
            match dims {
                None => dims = Some(header),
                Some(prev) => assert_eq!(prev, header, "coset files disagree on header ({path:?})"),
            }
            coset_maps.push(mmap);
        }
        let (num_columns, coset_size_log2, elem_bytes) = dims.unwrap();
        assert_eq!(
            elem_bytes,
            field_serialized_bytes::<F>(),
            "on-disk element width does not match this field"
        );
        Ok(Self {
            coset_maps,
            num_columns,
            coset_size_log2,
            elem_bytes,
            _marker: PhantomData,
        })
    }

    fn parse_header(mmap: &MemoryMappedFile) -> std::io::Result<(usize, usize, usize)> {
        let b = mmap
            .as_slice_bytes(0, RS_HEADER_BYTES as u64)
            .map_err(mmap_io_err)?;
        let magic = u32::from_le_bytes(b[0..4].try_into().unwrap());
        assert_eq!(magic, RS_CODEWORD_MAGIC, "bad RS-codeword magic");
        let elem_bytes = u32::from_le_bytes(b[4..8].try_into().unwrap()) as usize;
        let num_columns = u64::from_le_bytes(b[8..16].try_into().unwrap()) as usize;
        let coset_size_log2 = u64::from_le_bytes(b[16..24].try_into().unwrap()) as usize;
        Ok((num_columns, coset_size_log2, elem_bytes))
    }

    /// Zero-copy byte view of `count` contiguous elements starting at
    /// `element_index` within coset `coset`'s mapping.
    #[inline]
    fn element_bytes_run(&self, coset: usize, element_index: usize, count: usize) -> &[u8] {
        let start = (RS_HEADER_BYTES + element_index * self.elem_bytes) as u64;
        let len = (count * self.elem_bytes) as u64;
        self.coset_maps[coset]
            .as_slice_bytes(start, len)
            .expect("RS-codeword mmap access out of bounds")
    }

    /// Read a single element straight from the mmap.
    #[inline]
    fn element_at(&self, coset: usize, element_index: usize) -> F {
        read_field_le::<F>(self.element_bytes_run(coset, element_index, 1))
    }
}

impl<F: PrimeField + TwoAdicField> RSQueriable<F> for OnDiskRsCodewords<F> {
    fn num_columns(&self) -> usize {
        self.num_columns
    }

    fn num_cosets(&self) -> usize {
        self.coset_maps.len()
    }

    fn coset_size_log2(&self) -> usize {
        self.coset_size_log2
    }

    fn values_for_coset_and_index(
        &self,
        coset_in_natural_enumeration: usize,
        index: usize,
        values_per_leaf: usize,
    ) -> Vec<Vec<F>> {
        let coset_len = 1usize << self.coset_size_log2;
        let offsets = offsets_vec_for_leaf_construction(coset_len, values_per_leaf);
        // Offset-major `[offset][column]`, matching `ColumnMajorBaseOracleForCoset`.
        let mut result: Vec<Vec<F>> = (0..values_per_leaf)
            .map(|_| Vec::with_capacity(self.num_columns))
            .collect();
        for col in 0..self.num_columns {
            let col_base = col * coset_len;
            for (j, &off) in offsets.iter().enumerate() {
                result[j]
                    .push(self.element_at(coset_in_natural_enumeration, col_base + off + index));
            }
        }
        result
    }

    fn main_domain_column(&self, column_index: usize) -> MainDomainColumn<'_, F> {
        // Coset 0 is the main evaluation domain; its columns are EVALUATIONS. This is
        // the one full-column read (needed for batching); the bytes page in lazily
        // from the mmap and are converted in one contiguous pass.
        let coset_len = 1usize << self.coset_size_log2;
        let bytes = self.element_bytes_run(0, column_index * coset_len, coset_len);
        let column = bytes
            .chunks_exact(self.elem_bytes)
            .map(read_field_le::<F>)
            .collect();
        MainDomainColumn::Evals(Cow::Owned(column))
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

#[cfg(all(test, feature = "prover"))]
mod test {
    use super::*;
    use crate::gkr::prover::stages::commitment_utils::ColumnMajorCosetBoundTracePart;
    use field::baby_bear::base::BabyBearField;
    use field::{Field, PrimeField};
    use std::sync::Arc;

    fn bb(v: u32) -> BabyBearField {
        BabyBearField::from_raw_repr_with_reduction(v)
    }

    /// Serialize a `MaterializedCosets` to disk, memory-map it back with
    /// `OnDiskRsCodewords`, and require identical `values_for_coset_and_index`,
    /// `main_domain_column`, and dimensions.
    #[test]
    fn on_disk_rs_roundtrip_matches_materialized() {
        let num_cosets = 4usize;
        let num_columns = 3usize;
        let coset_size_log2 = 5usize;
        let coset_len = 1usize << coset_size_log2;

        let cosets: Vec<ColumnMajorBaseOracleForCoset<BabyBearField>> = (0..num_cosets)
            .map(|c| {
                let columns: Vec<ColumnMajorCosetBoundTracePart<BabyBearField, BabyBearField>> = (0
                    ..num_columns)
                    .map(|col| {
                        let data: Vec<BabyBearField> = (0..coset_len)
                            .map(|i| bb((c * 100000 + col * 1000 + i) as u32))
                            .collect();
                        ColumnMajorCosetBoundTracePart {
                            column: Arc::new(data.into_boxed_slice()),
                            offset: BabyBearField::ONE,
                        }
                    })
                    .collect();
                ColumnMajorBaseOracleForCoset {
                    original_values_normal_order: columns,
                    offset: BabyBearField::ONE,
                    coset_size_log2,
                }
            })
            .collect();
        let materialized = MaterializedCosets { cosets };

        let prefix = format!(
            "{}/rs_on_disk_roundtrip_test",
            std::env::temp_dir().display()
        );
        let paths = materialized
            .serialize_to_disk(&prefix)
            .expect("serialize cosets");
        assert_eq!(paths.len(), num_cosets);

        let reader = OnDiskRsCodewords::<BabyBearField>::open(paths.clone()).expect("open");

        assert_eq!(RSQueriable::num_columns(&reader), num_columns);
        assert_eq!(RSQueriable::num_cosets(&reader), num_cosets);
        assert_eq!(RSQueriable::coset_size_log2(&reader), coset_size_log2);

        for vpl in [2usize, 4, 8, 16] {
            let leaves = coset_len / vpl;
            for coset in 0..num_cosets {
                for index in 0..leaves {
                    let expected =
                        RSQueriable::values_for_coset_and_index(&materialized, coset, index, vpl);
                    let got = RSQueriable::values_for_coset_and_index(&reader, coset, index, vpl);
                    assert_eq!(got, expected, "vpl={vpl} coset={coset} index={index}");
                }
            }
        }

        for col in 0..num_columns {
            let expected = materialized.main_domain_column(col).into_owned();
            let got = RSQueriable::main_domain_column(&reader, col).into_owned();
            assert_eq!(got, expected, "main_domain_column col={col}");
        }

        // Drop the mmaps before removing the files.
        drop(reader);
        for p in paths {
            let _ = std::fs::remove_file(p);
        }
    }
}
