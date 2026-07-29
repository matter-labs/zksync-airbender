//! On-disk storage for base RS codewords (the `RSQueriable` side of a base/setup
//! commitment, mirroring the tree-side [`on_disk`](crate::merkle_trees::on_disk)).
//!
//! A single LDE coset serializes to a small header plus its columns concatenated
//! column-major as raw field-element bytes:
//!
//! ```text
//! [ header: magic(4) field_size(4) num_columns(8) coset_size_log2(8) ]
//! [ column 0: 2^coset_size_log2 field elements (raw bytes) ]
//! [ column 1: ... ]  ...
//! ```
//!
//! A full [`MaterializedCosets`] writes one such file per coset, sharing a common
//! path prefix. [`OnDiskRsCodewords`] reads them back lazily (positioned file
//! reads, no full load) as a [`RSQueriable`], so a base/setup oracle's RS codewords
//! can live on disk instead of in RAM. The values are laid out to serve
//! [`RSQueriable::values_for_coset_and_index`] with the same offset-major
//! `[offset][column]` shape as [`ColumnMajorBaseOracleForCoset`].
//!
//! Field elements are written in their in-memory representation (little-endian on
//! the host); these are local scratch files read back on the same build, so no
//! cross-host canonicalization is applied (consistent with the leaf-hash bytes in
//! the tree format only being meaningful locally).

use super::offsets_vec_for_leaf_construction;
use super::{ColumnMajorBaseOracleForCoset, MaterializedCosets};
use crate::merkle_trees::{MainDomainColumn, RSQueriable};
use field::{PrimeField, TwoAdicField};
use std::borrow::Cow;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};
use std::marker::PhantomData;
use std::path::{Path, PathBuf};

/// Magic marker ("RSC1") identifying a coset RS-codeword file.
pub const RS_CODEWORD_MAGIC: u32 = u32::from_le_bytes(*b"RSC1");

/// Header size in bytes: magic(4) + field_size(4) + num_columns(8) + coset_size_log2(8).
pub const RS_HEADER_BYTES: usize = 4 + 4 + 8 + 8;

/// Write a field slice as its raw in-memory bytes.
fn write_field_slice<F: Copy, W: Write>(writer: &mut W, data: &[F]) -> std::io::Result<()> {
    // SAFETY: `F` is `Copy` (a POD field element); we serialize its raw representation
    // and read it back with `read_unaligned` on the same build.
    let bytes = unsafe {
        core::slice::from_raw_parts(
            data.as_ptr() as *const u8,
            core::mem::size_of_val(data),
        )
    };
    writer.write_all(bytes)
}

/// Read one field element from a byte buffer at `byte_offset` (unaligned-safe).
#[inline]
fn read_field<F: Copy>(buf: &[u8], byte_offset: usize) -> F {
    debug_assert!(byte_offset + core::mem::size_of::<F>() <= buf.len());
    // SAFETY: bounds checked above; `read_unaligned` tolerates arbitrary alignment.
    unsafe { core::ptr::read_unaligned(buf.as_ptr().add(byte_offset) as *const F) }
}

/// Serialize a single coset's RS codewords (header + column-major raw bytes) into
/// `writer`.
pub fn serialize_coset<F, W>(
    coset: &ColumnMajorBaseOracleForCoset<F>,
    writer: &mut W,
) -> std::io::Result<()>
where
    F: PrimeField + TwoAdicField,
    W: Write,
{
    let num_columns = coset.original_values_normal_order.len();
    let coset_size_log2 = coset.coset_size_log2;
    let coset_len = 1usize << coset_size_log2;

    writer.write_all(&RS_CODEWORD_MAGIC.to_le_bytes())?;
    writer.write_all(&(core::mem::size_of::<F>() as u32).to_le_bytes())?;
    writer.write_all(&(num_columns as u64).to_le_bytes())?;
    writer.write_all(&(coset_size_log2 as u64).to_le_bytes())?;

    for col in coset.original_values_normal_order.iter() {
        assert_eq!(
            col.column.len(),
            coset_len,
            "coset column length must be 2^coset_size_log2"
        );
        write_field_slice(writer, &col.column[..])?;
    }
    Ok(())
}

impl<F: PrimeField + TwoAdicField> ColumnMajorBaseOracleForCoset<F> {
    /// Serialize this coset's RS codewords into any [`std::io::Write`] sink (see the
    /// module docs for the format).
    pub fn serialize_to_disk<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        serialize_coset(self, writer)
    }
}

/// File extension for a serialized coset RS-codeword file (RS CodeWord).
pub const RS_CODEWORD_FILE_EXT: &str = "rscw";

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
            let mut file = File::create(&path)?;
            serialize_coset(coset, &mut file)?;
            file.flush()?;
            paths.push(path);
        }
        Ok(paths)
    }
}

/// A [`RSQueriable`] backed by per-coset files on disk (as written by
/// [`MaterializedCosets::serialize_to_disk`]). Reads are lazy and positioned — only
/// the queried leaf elements (or, for `main_domain_column`, the one coset-0 column)
/// are read — so the full codeword never has to reside in RAM. Coset 0 is the main
/// evaluation domain.
#[derive(Debug)]
pub struct OnDiskRsCodewords<F: PrimeField + TwoAdicField> {
    coset_paths: Vec<PathBuf>,
    num_columns: usize,
    coset_size_log2: usize,
    _marker: PhantomData<fn() -> F>,
}

impl<F: PrimeField + TwoAdicField> OnDiskRsCodewords<F> {
    /// Open a set of coset files (in coset order; coset 0 = main domain) previously
    /// written for this field. Reads and validates each file's header.
    pub fn open(coset_paths: Vec<PathBuf>) -> std::io::Result<Self> {
        assert!(!coset_paths.is_empty(), "need at least one coset file");
        let mut num_columns = None;
        let mut coset_size_log2 = None;
        for path in coset_paths.iter() {
            let (nc, cs) = Self::read_header(path)?;
            match (num_columns, coset_size_log2) {
                (None, None) => {
                    num_columns = Some(nc);
                    coset_size_log2 = Some(cs);
                }
                (Some(pnc), Some(pcs)) => {
                    assert_eq!(pnc, nc, "coset files disagree on num_columns");
                    assert_eq!(pcs, cs, "coset files disagree on coset_size_log2");
                }
                _ => unreachable!(),
            }
        }
        Ok(Self {
            coset_paths,
            num_columns: num_columns.unwrap(),
            coset_size_log2: coset_size_log2.unwrap(),
            _marker: PhantomData,
        })
    }

    fn read_header(path: &Path) -> std::io::Result<(usize, usize)> {
        let mut file = File::open(path)?;
        let mut header = [0u8; RS_HEADER_BYTES];
        file.read_exact(&mut header)?;
        let magic = u32::from_le_bytes(header[0..4].try_into().unwrap());
        assert_eq!(magic, RS_CODEWORD_MAGIC, "bad RS-codeword magic in {path:?}");
        let field_size = u32::from_le_bytes(header[4..8].try_into().unwrap()) as usize;
        assert_eq!(
            field_size,
            core::mem::size_of::<F>(),
            "RS-codeword field size mismatch in {path:?}"
        );
        let num_columns = u64::from_le_bytes(header[8..16].try_into().unwrap()) as usize;
        let coset_size_log2 = u64::from_le_bytes(header[16..24].try_into().unwrap()) as usize;
        Ok((num_columns, coset_size_log2))
    }

    /// Byte offset of element `element_index` within a coset file.
    #[inline]
    fn element_byte_offset(&self, element_index: usize) -> u64 {
        (RS_HEADER_BYTES + element_index * core::mem::size_of::<F>()) as u64
    }

    /// Read `count` contiguous elements starting at `element_index` from coset
    /// `coset` into a `Vec<F>`.
    fn read_run(&self, coset: usize, element_index: usize, count: usize) -> Vec<F> {
        let fsize = core::mem::size_of::<F>();
        let mut file = File::open(&self.coset_paths[coset])
            .unwrap_or_else(|e| panic!("open coset {coset}: {e}"));
        file.seek(SeekFrom::Start(self.element_byte_offset(element_index)))
            .expect("seek");
        let mut buf = vec![0u8; count * fsize];
        file.read_exact(&mut buf).expect("read coset run");
        (0..count).map(|i| read_field::<F>(&buf, i * fsize)).collect()
    }
}

impl<F: PrimeField + TwoAdicField> RSQueriable<F> for OnDiskRsCodewords<F> {
    fn num_columns(&self) -> usize {
        self.num_columns
    }

    fn num_cosets(&self) -> usize {
        self.coset_paths.len()
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

        // Read all needed elements once per file, then reshape offset-major
        // `[offset][column]` (matching `ColumnMajorBaseOracleForCoset`).
        let mut result: Vec<Vec<F>> = (0..values_per_leaf)
            .map(|_| Vec::with_capacity(self.num_columns))
            .collect();
        let fsize = core::mem::size_of::<F>();
        let mut file = File::open(&self.coset_paths[coset_in_natural_enumeration])
            .unwrap_or_else(|e| panic!("open coset {coset_in_natural_enumeration}: {e}"));
        for col in 0..self.num_columns {
            let col_base = col * coset_len;
            for (j, &off) in offsets.iter().enumerate() {
                let element_index = col_base + off + index;
                file.seek(SeekFrom::Start(self.element_byte_offset(element_index)))
                    .expect("seek");
                let mut buf = vec![0u8; fsize];
                file.read_exact(&mut buf).expect("read leaf element");
                result[j].push(read_field::<F>(&buf, 0));
            }
        }
        result
    }

    fn main_domain_column(&self, column_index: usize) -> MainDomainColumn<'_, F> {
        // Coset 0 is the main evaluation domain; its columns are EVALUATIONS.
        let coset_len = 1usize << self.coset_size_log2;
        let column = self.read_run(0, column_index * coset_len, coset_len);
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

    /// Serialize a `MaterializedCosets` to disk, read it back with
    /// `OnDiskRsCodewords`, and require identical `values_for_coset_and_index`,
    /// `main_domain_column`, and dimensions.
    #[test]
    fn on_disk_rs_roundtrip_matches_materialized() {
        let num_cosets = 4usize;
        let num_columns = 3usize;
        let coset_size_log2 = 5usize;
        let coset_len = 1usize << coset_size_log2;

        // Distinct value per (coset, column, position) so mismatches are visible.
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
                    let expected = RSQueriable::values_for_coset_and_index(
                        &materialized,
                        coset,
                        index,
                        vpl,
                    );
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

        for p in paths {
            let _ = std::fs::remove_file(p);
        }
    }
}
