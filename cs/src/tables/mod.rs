use crate::definitions::MAX_TABLE_WIDTH;
use arrayvec::ArrayVec;
use core::panic;
use derivative::Derivative;
use field::PrimeField;
use rayon::prelude::*;
use smallvec::SmallVec;
use std::sync::{LazyLock, Mutex};
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};
use type_map::concurrent::TypeMap;

mod binops;
mod integer_ops;
mod jump_branch_opcode_related;
mod keccak_precompile_related;
mod memory_opcode_related;
// mod range_checks_and_decompositions;
mod quote;
mod rom_related;
mod shift_opcode_related;
mod zero_entry;

pub use self::binops::*;
pub use self::integer_ops::*;
pub use self::jump_branch_opcode_related::*;
pub use self::keccak_precompile_related::*;
pub use self::memory_opcode_related::*;
// pub use self::range_checks_and_decompositions::*;
pub use self::rom_related::*;
pub use self::shift_opcode_related::*;
pub use self::zero_entry::*;

pub use super::definitions::TableType;

const TOTAL_NUM_OF_TABLES: usize = TableType::DynamicPlaceholder as u32 as usize;

// NOTE: we follow the convention to pass keys and return values in a padded form,
// so it's always fixed size, but "unused" values are 0s

// keys -> index in table and values
pub type PureTableGenerationFn<F: PrimeField> = fn(&[F]) -> (usize, ArrayVec<F, MAX_TABLE_WIDTH>);
pub type TableGenerationClosure<F: PrimeField> = std::sync::Arc<
    dyn Fn(&[F]) -> (usize, ArrayVec<F, MAX_TABLE_WIDTH>)
        + 'static
        + Send
        + Sync
        + std::panic::UnwindSafe
        + std::panic::RefUnwindSafe,
>;

#[derive(Derivative)]
#[derivative(Clone)]
pub enum ValueLookupFn<F: PrimeField> {
    None,
    Pure(fn(&[F]) -> ArrayVec<F, MAX_TABLE_WIDTH>),
    ReuseGenerationFn(PureTableGenerationFn<F>),
    Closure(TableGenerationClosure<F>),
}

#[derive(Derivative)]
#[derivative(Clone)]
pub enum IndexLookupFn<F: PrimeField> {
    None,
    Pure(fn(&[F]) -> usize),
    ReuseGenerationFn(PureTableGenerationFn<F>),
    ReuseGenerationClosure(TableGenerationClosure<F>),
    Closure(std::sync::Arc<dyn Fn(&[F]) -> usize + 'static + Send + Sync>),
}

pub const TABLE_TYPES_UPPER_BOUNDS: usize = TOTAL_NUM_OF_TABLES;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct LookupTable<F: PrimeField> {
    pub name: String,
    pub num_key_columns: usize,
    pub num_value_columns: usize,
    // NOTE: for small fields and not too large N hashmaps are the most efficient here

    // to lookup value from key
    #[derivative(Debug = "ignore")]
    pub lookup_data: Arc<HashMap<LookupKey<F>, LookupValue<F>>>,
    // to lookup table index from full row
    #[derivative(Debug = "ignore")]
    pub content_data: Arc<HashMap<ArrayVec<F, MAX_TABLE_WIDTH>, usize>>,
    // for setup - plain content of the table
    #[derivative(Debug = "ignore")]
    pub data: Arc<Vec<ArrayVec<F, MAX_TABLE_WIDTH>>>,
    #[derivative(Debug = "ignore")]
    pub quick_value_lookup_fn: ValueLookupFn<F>,
    #[derivative(Debug = "ignore")]
    pub quick_index_lookup_fn: IndexLookupFn<F>,

    pub id: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LookupKey<F: PrimeField>(ArrayVec<F, MAX_TABLE_WIDTH>);

pub type LookupValue<F> = LookupKey<F>;

impl<F: PrimeField> LookupKey<F> {
    fn from_keys(keys: &[F]) -> Self {
        let mut new = ArrayVec::new();
        new.try_extend_from_slice(keys).expect("length fits");

        Self(new)
    }
}

impl<F: PrimeField> PartialOrd for LookupKey<F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.0.len() != other.0.len() {
            return Some(std::cmp::Ordering::Less);
        }
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            match a.as_u32_reduced().cmp(&b.as_u32_reduced()) {
                std::cmp::Ordering::Equal => {
                    continue;
                }
                ordering @ _ => {
                    return Some(ordering);
                }
            }
        }

        panic!("most likely duplicate entries in the table");
    }
}
impl<F: PrimeField> Ord for LookupKey<F> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.0.len() != other.0.len() {
            return std::cmp::Ordering::Less;
        }
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            match a.as_u32_reduced().cmp(&b.as_u32_reduced()) {
                std::cmp::Ordering::Equal => {
                    continue;
                }
                ordering @ _ => {
                    return ordering;
                }
            }
        }

        std::cmp::Ordering::Equal
    }
}

impl<F: PrimeField> LookupTable<F> {
    #[allow(unused)]
    fn check_well_formed(data: &[ArrayVec<F, MAX_TABLE_WIDTH>]) -> bool {
        // just use hash table to check that entries are unique
        let mut tmp = HashSet::new();
        for el in data.iter() {
            let is_unique = tmp.insert(el.clone());
            if is_unique == false {
                return false;
            }
        }

        true
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    #[inline]
    pub fn table_size(&self) -> usize {
        self.content_data.len()
    }

    pub(crate) fn create_table_from_key_and_pure_generation_fn<
        K: AsRef<[F]> + Send + Sync + 'static,
    >(
        keys: &Vec<K>,
        name: String,
        num_key_columns: usize,
        num_value_columns: usize,
        table_gen_func: PureTableGenerationFn<F>,
        index_gen_fn: Option<fn(&[F]) -> usize>,
        id: u32,
    ) -> Self {
        assert!(num_key_columns + num_value_columns + 1 <= MAX_TABLE_WIDTH);

        let mut content = Vec::with_capacity(keys.len());
        if keys.len() < 1 << 14 {
            for key in keys.iter() {
                let (_index, values) = table_gen_func(key.as_ref());
                assert_eq!(key.as_ref().len(), num_key_columns);
                assert_eq!(values.len(), num_value_columns);
                let mut row = ArrayVec::<F, MAX_TABLE_WIDTH>::new();
                row.try_extend_from_slice(&key.as_ref()[..num_key_columns])
                    .expect("keys must fit");
                row.try_extend_from_slice(&values[..num_value_columns])
                    .expect("values must fit");
                content.push(row);
            }
        } else {
            keys.par_iter()
                .map(|key: &K| {
                    let (_index, values) = table_gen_func(key.as_ref());
                    assert_eq!(key.as_ref().len(), num_key_columns);
                    assert_eq!(values.len(), num_value_columns);
                    let mut row = ArrayVec::<F, MAX_TABLE_WIDTH>::new();
                    row.try_extend_from_slice(&key.as_ref()[..num_key_columns])
                        .expect("keys must fit");
                    row.try_extend_from_slice(&values[..num_value_columns])
                        .expect("values must fit");
                    row
                })
                .collect_into_vec(&mut content);
        }

        let (lookup_data, content_data) =
            Self::compute_default_lookup_impls(&content, num_key_columns, num_value_columns);

        let index_gen_fn = if let Some(index_gen_fn) = index_gen_fn {
            IndexLookupFn::Pure(index_gen_fn)
        } else {
            IndexLookupFn::ReuseGenerationFn(table_gen_func)
        };

        Self {
            name,
            lookup_data: Arc::new(lookup_data),
            content_data: Arc::new(content_data),
            data: Arc::new(content),
            quick_value_lookup_fn: ValueLookupFn::ReuseGenerationFn(table_gen_func),
            quick_index_lookup_fn: index_gen_fn,
            num_key_columns,
            num_value_columns,
            id,
        }
    }

    pub(crate) fn create_table_from_key_and_key_generation_closure<
        K: AsRef<[F]> + Send + Sync + 'static,
        FN: Fn(&[F]) -> (usize, ArrayVec<F, MAX_TABLE_WIDTH>)
            + 'static
            + Send
            + Sync
            + Clone
            + std::panic::UnwindSafe
            + std::panic::RefUnwindSafe,
    >(
        keys: &Vec<K>,
        name: String,
        num_key_columns: usize,
        num_value_columns: usize,
        table_gen_closure: FN,
        index_gen_fn: Option<fn(&[F]) -> usize>,
        id: u32,
    ) -> Self {
        assert!(num_key_columns + num_value_columns + 1 <= MAX_TABLE_WIDTH);

        let mut content = Vec::with_capacity(keys.len());
        if keys.len() < 1 << 14 {
            for key in keys.iter() {
                let (_index, values) = table_gen_closure(key.as_ref());
                assert_eq!(key.as_ref().len(), num_key_columns);
                assert_eq!(values.len(), num_value_columns);
                let mut row = ArrayVec::<F, MAX_TABLE_WIDTH>::new();
                row.try_extend_from_slice(&key.as_ref()[..num_key_columns])
                    .expect("keys must fit");
                row.try_extend_from_slice(&values[..num_value_columns])
                    .expect("values must fit");
                content.push(row);
            }
        } else {
            keys.par_iter()
                .map(|key: &K| {
                    let (_index, values) = table_gen_closure(key.as_ref());
                    assert_eq!(key.as_ref().len(), num_key_columns);
                    assert_eq!(values.len(), num_value_columns);
                    let mut row = ArrayVec::<F, MAX_TABLE_WIDTH>::new();
                    row.try_extend_from_slice(&key.as_ref()[..num_key_columns])
                        .expect("keys must fit");
                    row.try_extend_from_slice(&values[..num_value_columns])
                        .expect("values must fit");
                    row
                })
                .collect_into_vec(&mut content);
        }

        let (lookup_data, content_data) =
            Self::compute_default_lookup_impls(&content, num_key_columns, num_value_columns);

        let index_gen_fn = if let Some(index_gen_fn) = index_gen_fn {
            IndexLookupFn::Pure(index_gen_fn)
        } else {
            IndexLookupFn::ReuseGenerationClosure(Arc::new(table_gen_closure.clone()))
        };

        Self {
            name,
            lookup_data: Arc::new(lookup_data),
            content_data: Arc::new(content_data),
            data: Arc::new(content),
            quick_value_lookup_fn: ValueLookupFn::Closure(Arc::new(table_gen_closure)),
            quick_index_lookup_fn: index_gen_fn,
            num_key_columns,
            num_value_columns,
            id,
        }
    }

    fn compute_default_lookup_impls(
        data: &Vec<ArrayVec<F, MAX_TABLE_WIDTH>>,
        num_key_columns: usize,
        num_value_columns: usize,
    ) -> (
        HashMap<LookupKey<F>, LookupValue<F>>,
        HashMap<ArrayVec<F, MAX_TABLE_WIDTH>, usize>,
    ) {
        let lookup_data: HashMap<LookupKey<F>, LookupValue<F>> =
            Self::compute_lookup_data(data, num_key_columns, num_value_columns);
        let content_data: HashMap<_, _> = data
            .par_iter()
            .enumerate()
            .map(|(idx, el)| (el.clone(), idx))
            .collect();

        (lookup_data, content_data)
    }

    /// Splits data elements into key, value.
    /// We treat first num_key_columns elements from each data item
    /// as key, and the rest as value.
    fn compute_lookup_data(
        data: &Vec<ArrayVec<F, MAX_TABLE_WIDTH>>,
        num_key_columns: usize,
        num_value_columns: usize,
    ) -> HashMap<LookupKey<F>, LookupValue<F>> {
        assert!(num_key_columns + num_value_columns + 1 <= MAX_TABLE_WIDTH);
        let result: HashMap<_, _> = data
            .par_iter()
            .map(|row| {
                let key = LookupKey::from_keys(&row[..num_key_columns]);
                let value = LookupValue::from_keys(&row[num_key_columns..]);
                (key, value)
            })
            .collect();
        assert_eq!(
            result.len(),
            data.len(),
            "Can't compute lookup cache if using only {} first columns out of {} as logical key",
            num_key_columns,
            num_key_columns + num_value_columns,
        );
        result
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup_value<const VALUES: usize>(&self, keys: &[F]) -> [F; VALUES] {
        // Originally this path required an exact key arity match:
        // assert_eq!(keys.len(), self.num_key_columns);
        //
        // We now allow callers of dynamic-sized lookups to pass trailing zero
        // slack columns, and truncate them before dispatching into the selected
        // table shape.
        assert!(
            keys.len() >= self.num_key_columns,
            "lookup for table {} received {} key columns, but requires at least {}",
            self.name(),
            keys.len(),
            self.num_key_columns
        );
        assert!(
            keys[self.num_key_columns..].iter().all(|el| *el == F::ZERO),
            "lookup for table {} received non-zero extra key columns beyond {}",
            self.name(),
            self.num_key_columns
        );
        let keys = &keys[..self.num_key_columns];
        assert!(VALUES < MAX_TABLE_WIDTH);
        // NOTE that lookup function return padded values in generation functions
        match &self.quick_value_lookup_fn {
            ValueLookupFn::None => {
                let keys = LookupKey::from_keys(keys);
                let Some(values) = self.lookup_data.get(&keys).cloned() else {
                    panic!(
                        "There is no value for key {:?} for table {}",
                        keys,
                        self.name()
                    );
                };
                // Originally this path required an exact value arity match:
                // assert_eq!(values.0.len(), VALUES);
                //
                // Dynamic-sized lookups may target narrower or wider tables. We
                // allow missing outputs to be padded with zeroes, and only allow
                // extra returned outputs if they are also zero-valued slack.
                assert!(
                    values.0.len() <= VALUES
                        || values.0[VALUES..].iter().all(|el| *el == F::ZERO),
                    "lookup for table {} returned {} values, but caller expects {}; extra returned values must be zero",
                    self.name(),
                    values.0.len(),
                    VALUES
                );

                std::array::from_fn(|i| values.0.get(i).copied().unwrap_or(F::ZERO))
            }
            ValueLookupFn::Pure(..) => {
                unimplemented!()
            }
            ValueLookupFn::ReuseGenerationFn(gen_fn) => {
                let (_, values) = (gen_fn)(keys);
                // Originally this path required an exact value arity match:
                // assert_eq!(values.len(), VALUES);
                assert!(
                    values.len() <= VALUES || values[VALUES..].iter().all(|el| *el == F::ZERO),
                    "lookup for table {} returned {} values, but caller expects {}; extra returned values must be zero",
                    self.name(),
                    values.len(),
                    VALUES
                );

                std::array::from_fn(|i| values.get(i).copied().unwrap_or(F::ZERO))
            }
            ValueLookupFn::Closure(gen_closure) => {
                let (_, values) = (gen_closure)(keys);
                // Originally this path required an exact value arity match:
                // assert_eq!(values.len(), VALUES);
                assert!(
                    values.len() <= VALUES || values[VALUES..].iter().all(|el| *el == F::ZERO),
                    "lookup for table {} returned {} values, but caller expects {}; extra returned values must be zero",
                    self.name(),
                    values.len(),
                    VALUES
                );

                std::array::from_fn(|i| values.get(i).copied().unwrap_or(F::ZERO))
            }
        }
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup_values_and_get_index<const VALUES: usize>(
        &self,
        keys: &[F],
    ) -> (usize, [F; VALUES]) {
        // Originally this path required an exact key arity match:
        // assert_eq!(keys.len(), self.num_key_columns);
        //
        // We now allow callers of dynamic-sized lookups to pass trailing zero
        // slack columns, and truncate them before dispatching into the selected
        // table shape.
        assert!(
            keys.len() >= self.num_key_columns,
            "lookup for table {} received {} key columns, but requires at least {}",
            self.name(),
            keys.len(),
            self.num_key_columns
        );
        assert!(
            keys[self.num_key_columns..].iter().all(|el| *el == F::ZERO),
            "lookup for table {} received non-zero extra key columns beyond {}",
            self.name(),
            self.num_key_columns
        );
        let keys = &keys[..self.num_key_columns];
        assert!(VALUES < MAX_TABLE_WIDTH);
        // NOTE that lookup function return padded values in generation functions
        match &self.quick_value_lookup_fn {
            ValueLookupFn::None => {
                let keys = LookupKey::from_keys(keys);
                let Some(_values) = self.lookup_data.get(&keys).cloned() else {
                    panic!(
                        "There is no value for key {:?} for table {}",
                        keys,
                        self.name()
                    );
                };

                todo!();

                // std::array::from_fn(|i| value.0[i])
            }
            ValueLookupFn::Pure(..) => {
                unimplemented!()
            }
            ValueLookupFn::ReuseGenerationFn(gen_fn) => {
                let (index, values) = (gen_fn)(keys);
                // Originally this path required an exact value arity match:
                // assert_eq!(values.len(), VALUES);
                assert!(
                    values.len() <= VALUES || values[VALUES..].iter().all(|el| *el == F::ZERO),
                    "lookup for table {} returned {} values, but caller expects {}; extra returned values must be zero",
                    self.name(),
                    values.len(),
                    VALUES
                );

                (
                    index,
                    std::array::from_fn(|i| values.get(i).copied().unwrap_or(F::ZERO)),
                )
            }
            ValueLookupFn::Closure(gen_closure) => {
                let (index, values) = (gen_closure)(keys);
                // Originally this path required an exact value arity match:
                // assert_eq!(values.len(), VALUES);
                assert!(
                    values.len() <= VALUES || values[VALUES..].iter().all(|el| *el == F::ZERO),
                    "lookup for table {} returned {} values, but caller expects {}; extra returned values must be zero",
                    self.name(),
                    values.len(),
                    VALUES
                );

                (
                    index,
                    std::array::from_fn(|i| values.get(i).copied().unwrap_or(F::ZERO)),
                )
            }
        }
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup_row(&self, key: &[F]) -> usize {
        let key = if key.len() >= self.width() {
            for el in key[self.width()..].iter() {
                assert!(el.is_zero());
            }
            &key[..self.width()]
        } else {
            // key is shorter than the table, that may happen in special case of zero entry
            // table, and so we hardcode it blindly
            assert_eq!(self.table_size(), 1);
            for el in key.iter() {
                assert!(el.is_zero());
            }

            return 0;
        };

        match &self.quick_index_lookup_fn {
            IndexLookupFn::None => {
                let mut keys = ArrayVec::<F, MAX_TABLE_WIDTH>::new();
                keys.try_extend_from_slice(key).expect("must fit");
                self.content_data
                    .get(&keys)
                    .copied()
                    .expect("element must be present in the table")
            }
            IndexLookupFn::Pure(index_fn) => {
                let index = (index_fn)(key);
                assert!(
                    index < self.table_size(),
                    "index {} is beyond table size {} for table {}",
                    index,
                    self.table_size(),
                    &self.name
                );

                index
            }
            IndexLookupFn::ReuseGenerationFn(gen_fn) => {
                // NOTE: generation functions do not use padding places, so we can feed as-is
                let (index, values) = (gen_fn)(key);
                // can self-check
                assert_eq!(
                    &values[..self.num_value_columns],
                    &key[self.num_key_columns..][..self.num_key_columns]
                );
                assert!(
                    index < self.table_size(),
                    "index {} is beyond table size {} for table {}",
                    index,
                    self.table_size(),
                    &self.name
                );

                index
            }
            IndexLookupFn::ReuseGenerationClosure(gen_closure) => {
                // NOTE: generation functions do not use padding places, so we can feed as-is
                let (index, values) = (gen_closure)(key);
                // can self-check
                assert_eq!(
                    &values[..self.num_value_columns],
                    &key[self.num_key_columns..][..self.num_key_columns]
                );
                assert!(
                    index < self.table_size(),
                    "index {} is beyond table size {} for table {}",
                    index,
                    self.table_size(),
                    &self.name
                );

                index
            }
            IndexLookupFn::Closure(..) => {
                unimplemented!()
            }
        }
    }

    pub fn num_values(&self) -> usize {
        self.num_value_columns
    }

    pub fn num_keys(&self) -> usize {
        self.num_key_columns
    }

    pub fn width(&self) -> usize {
        self.num_key_columns + self.num_value_columns
    }

    pub fn data_at_row(&self, row: usize) -> &[F] {
        &self.data[row][..]
    }

    pub fn dump_into(
        &self,
        dst: &mut Vec<ArrayVec<F, MAX_TABLE_WIDTH>>,
        id: Option<u32>,
        total_width_including_id: usize,
    ) {
        assert!(total_width_including_id > 0);
        assert!(
            self.width() < total_width_including_id,
            "trying to dump table `{}` of width {} into trace of width {} (with table ID)",
            self.name,
            self.width(),
            total_width_including_id
        );
        let required_len = self.width() + id.is_some() as usize;
        assert!(required_len <= total_width_including_id);
        assert!(required_len <= MAX_TABLE_WIDTH);
        let padding_width = if id.is_some() {
            total_width_including_id - 1
        } else {
            total_width_including_id
        };
        for row in self.data.iter() {
            let mut assembled_row = row.clone();
            assert_eq!(row.len(), self.width());
            assert!(self.width() <= padding_width);
            for _ in self.width()..padding_width {
                assembled_row.push(F::ZERO);
            }
            if let Some(id) = id {
                assembled_row.push(F::from_u32_unchecked(id as u32));
            }
            dst.push(assembled_row);
        }
    }

    // pub fn dump_limited_columns<const M: usize>(&self, dst: &mut Vec<[F; M]>) {
    //     for row in self.data.iter() {
    //         let mut assembled_row = [F::ZERO; M];
    //         assembled_row[..].copy_from_slice(&row[..M]);
    //         dst.push(assembled_row);
    //     }
    // }
}

#[derive(Clone, Debug)]
pub enum LookupWrapper<F: PrimeField> {
    Uninitialized,
    Initialized(LookupTable<F>),
}
impl<F: PrimeField> LookupWrapper<F> {
    pub fn is_initialized(&self) -> bool {
        match self {
            Self::Uninitialized => false,
            _ => true,
        }
    }

    pub fn width(&self) -> usize {
        match self {
            Self::Initialized(table) => table.width(),
            Self::Uninitialized => 0,
        }
    }

    pub fn get_table_id(&self) -> u32 {
        match self {
            LookupWrapper::Initialized(table) => table.id,
            Self::Uninitialized => {
                panic!("Trying to lookup into uninitialized table wrapper");
            }
        }
    }

    #[track_caller]
    #[inline]
    pub fn lookup_value<const VALUES: usize>(&self, keys: &[F]) -> [F; VALUES] {
        match self {
            Self::Initialized(inner) => inner.lookup_value::<VALUES>(keys),
            Self::Uninitialized => {
                panic!("Trying to lookup into uninitialized table wrapper");
            }
        }
    }

    #[track_caller]
    #[inline]
    pub fn lookup_values_and_get_index<const VALUES: usize>(
        &self,
        keys: &[F],
    ) -> (usize, [F; VALUES]) {
        match self {
            Self::Initialized(inner) => inner.lookup_values_and_get_index::<VALUES>(keys),
            Self::Uninitialized => {
                panic!("Table is not initialized");
            }
        }
    }

    #[track_caller]
    #[inline]
    pub fn lookup_row(&self, row: &[F]) -> usize {
        match self {
            Self::Initialized(inner) => inner.lookup_row(row),
            Self::Uninitialized => {
                panic!("Trying to lookup into uninitialized table wrapper");
            }
        }
    }

    pub fn get_size(&self) -> usize {
        match self {
            Self::Initialized(inner) => inner.table_size(),
            Self::Uninitialized => 0,
        }
    }

    // pub fn data_at_row(&self, row: usize) -> &[F] {
    //     match self {
    //         Self::Initialized(inner) => inner.data_at_row(row),
    //         Self::Uninitialized => &[],
    //     }
    // }

    pub fn dump_into(
        &self,
        dst: &mut Vec<ArrayVec<F, MAX_TABLE_WIDTH>>,
        id: Option<u32>,
        total_width_including_id: usize,
    ) {
        match self {
            Self::Initialized(inner) => inner.dump_into(dst, id, total_width_including_id),
            Self::Uninitialized => {}
        }
    }

    // pub fn dump_limited_columns<const N: usize>(&self, dst: &mut Vec<ArrayVec<F, MAX_TABLE_WIDTH>>) {
    //     match self {
    //         Self::Initialized(inner) => inner.dump_limited_columns::<N>(dst),
    //         Self::Uninitialized => {}
    //     }
    // }
}

// -------------------------------------Tables Realization------------------------------------
// -------------------------------------------------------------------------------------------

impl TableType {
    pub fn to_table_id(&self) -> u32 {
        *self as u32
    }

    pub fn to_num<F: PrimeField>(&self) -> crate::types::Num<F> {
        crate::types::Num::Constant(F::from_u32(*self as u32).expect("must fit"))
    }

    pub fn generate_table<F: PrimeField, const TOTAL_WIDTH: usize>(self) -> LookupWrapper<F> {
        let id = self.to_table_id();
        match self {
            TableType::ZeroEntry => {
                // LookupWrapper::Initialized(create_zero_entry_table::<F, TOTAL_WIDTH>(id))
                // WE DON'T WANT TO RESTRICT OURSELVES TO SPECIFIC NUMBER OF OUTPUTS
                LookupWrapper::Initialized(create_zero_entry_table::<F, 0>(id))
            }
            TableType::RegIsZero => LookupWrapper::Initialized(create_reg_is_zero_table::<F>(id)),
            TableType::U16GetSign => LookupWrapper::Initialized(create_u16_get_sign_table::<F>(id)),
            TableType::TruncateShiftAmountAndRangeCheck8 => LookupWrapper::Initialized(
                create_truncate_shift_amount_and_range_check_8_table::<F>(id),
            ),
            TableType::GetSignExtensionByte => {
                LookupWrapper::Initialized(create_sign_extension_byte_table::<F>(id))
            }
            TableType::And => LookupWrapper::Initialized(create_and_table::<F>(id)),
            TableType::Xor => LookupWrapper::Initialized(create_xor_table::<F, 8>(id)),
            TableType::Or => LookupWrapper::Initialized(create_or_table::<F>(id)),
            TableType::ConditionalJmpBranchSlt => {
                LookupWrapper::Initialized(create_conditional_op_resolution_table(id))
            }
            TableType::JumpCleanupOffset => {
                LookupWrapper::Initialized(create_jump_cleanup_offset_table(id))
            }
            TableType::ShiftImplementationOverBytes => {
                LookupWrapper::Initialized(create_shift_implementation_table::<F>(id))
            }
            // TableType::RangeCheck8x8 => LookupWrapper::Dimensional3(
            //     create_formal_width_3_range_check_table_for_two_tuple::<F, 8>(id),
            // ),
            // TableType::AndNot => LookupWrapper::Dimensional3(create_and_not_table(id)),
            // TableType::QuickDecodeDecompositionCheck4x4x4 => {
            //     LookupWrapper::Dimensional3(create_quick_decoder_decomposition_table_4x4x4(id))
            // }
            // TableType::QuickDecodeDecompositionCheck7x3x6 => {
            //     LookupWrapper::Dimensional3(create_quick_decoder_decomposition_table_7x3x6(id))
            // }
            // TableType::U16GetSignAndHighByte => {
            //     LookupWrapper::Dimensional3(create_u16_get_sign_and_high_byte_table(id))
            // }

            // TableType::MemoryOffsetGetBits => {
            //     LookupWrapper::Dimensional3(create_memory_offset_lowest_bits_table(id))
            // }
            // TableType::MemoryLoadGetSigns => {
            //     LookupWrapper::Dimensional3(create_memory_load_signs_table(id))
            // }
            // TableType::SRASignFiller => {
            //     LookupWrapper::Dimensional3(create_sra_sign_filler_table(id))
            // }
            // TableType::ConditionalOpAllConditionsResolver => {
            //     LookupWrapper::Dimensional3(create_conditional_op_resolution_table(id))
            // }
            // TableType::RomAddressSpaceSeparator => {
            //     unimplemented!("must manually generate a table to customize number of bits");
            //     // LookupWrapper::Dimensional3(create_rom_separator_table::<
            //     //     F,
            //     //     ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
            //     // >(id))
            // }
            // TableType::SpecialCSRProperties => {
            //     unimplemented!("must be created in a special manner");
            // }
            TableType::Xor3 => LookupWrapper::Initialized(create_xor_table::<F, 3>(id)),
            TableType::Xor4 => LookupWrapper::Initialized(create_xor_table::<F, 4>(id)),
            TableType::Xor7 => LookupWrapper::Initialized(create_xor_table::<F, 7>(id)),
            TableType::Xor9 => LookupWrapper::Initialized(create_xor_table::<F, 9>(id)),
            // TableType::Xor12 => LookupWrapper::Dimensional3(create_xor_table::<F, 12>(id)),
            // TableType::U16SplitAsBytes => {
            //     LookupWrapper::Dimensional3(create_u16_split_into_bytes_table(id))
            // }
            TableType::RangeCheck9x9 => {
                LookupWrapper::Initialized(create_range_check_table_for_two_tuple::<F, 9>(id))
            }
            TableType::RangeCheck10x10 => {
                LookupWrapper::Initialized(create_range_check_table_for_two_tuple::<F, 10>(id))
            }
            TableType::RangeCheck11 => {
                LookupWrapper::Initialized(create_range_check_table_for_single_entry::<F, 11>(id))
            }
            TableType::RangeCheck12 => {
                LookupWrapper::Initialized(create_range_check_table_for_single_entry::<F, 12>(id))
            }
            TableType::RangeCheck13 => {
                LookupWrapper::Initialized(create_range_check_table_for_single_entry::<F, 13>(id))
            }
            TableType::U16GetLowByte => {
                LookupWrapper::Initialized(create_u16_get_low_byte_table::<F>(id))
            }
            // TableType::ShiftImplementation => {
            //     LookupWrapper::Dimensional3(create_shift_implementation_table::<F>(id))
            // }
            // TableType::U16SelectByteAndGetByteSign => {
            //     LookupWrapper::Dimensional3(create_select_byte_and_get_sign_table::<F>(id))
            // }
            // TableType::ExtendLoadedValue => {
            //     LookupWrapper::Dimensional3(create_mem_load_extend_table::<F>(id))
            // }
            TableType::StoreByteSourceContribution => {
                LookupWrapper::Initialized(create_store_byte_source_contribution_table::<F>(id))
            }
            TableType::StoreByteExistingContribution => {
                LookupWrapper::Initialized(create_store_byte_existing_contribution_table::<F>(id))
            }
            TableType::LoadHalfwordSignextend => {
                LookupWrapper::Initialized(create_load_halfword_signextend_table::<F>(id))
            }
            TableType::LoadByteSignextend => {
                LookupWrapper::Initialized(create_load_byte_signextend_table::<F>(id))
            }
            // TableType::TruncateShift => {
            //     LookupWrapper::Dimensional3(create_truncate_shift_amount_table::<F>(id))
            // }
            // TableType::ConditionalJmpBranchSlt => LookupWrapper::Dimensional3(
            //     create_conditional_jmp_branch_slt_family_resolution_table(id),
            // ),
            // TableType::MemoryGetOffsetAndMaskWithTrap => {
            //     LookupWrapper::Dimensional3(create_memory_offset_mask_with_trap_table(id))
            // }
            // TableType::MemoryLoadHalfwordOrByte => {
            //     LookupWrapper::Dimensional3(create_memory_load_halfword_or_byte_table(id))
            // }
            // TableType::MemStoreClearOriginalRamValueLimb => LookupWrapper::Dimensional3(
            //     create_memory_store_halfword_or_byte_clear_source_limb_table::<F>(id),
            // ),
            // TableType::MemStoreClearWrittenValueLimb => LookupWrapper::Dimensional3(
            //     create_memory_store_halfword_or_byte_clear_written_limb_table::<F>(id),
            // ),
            // TableType::TruncateShiftAmount => {
            //     LookupWrapper::Dimensional3(create_shift_amount_truncation_table::<F>(id))
            // }
            // TableType::SllWith16BitInputLow => LookupWrapper::Dimensional3(
            //     create_logical_shift_16_bit_table::<F, false, false>(id),
            // ),
            // TableType::SllWith16BitInputHigh => {
            //     LookupWrapper::Dimensional3(create_logical_shift_16_bit_table::<F, true, false>(id))
            // }
            // TableType::SrlWith16BitInputLow => {
            //     LookupWrapper::Dimensional3(create_logical_shift_16_bit_table::<F, false, true>(id))
            // }
            // TableType::SrlWith16BitInputHigh => {
            //     LookupWrapper::Dimensional3(create_logical_shift_16_bit_table::<F, true, true>(id))
            // }
            // TableType::Sra16BitInputSignFill => {
            //     LookupWrapper::Dimensional3(create_sra_16_filler_mask_table::<F>(id))
            // }
            // TableType::RangeCheck16WithZeroPads => LookupWrapper::Dimensional3(
            //     create_formal_width_3_range_check_table_for_single_entry::<F, 16>(id),
            // ),
            TableType::KeccakPermutationIndices => {
                LookupWrapper::Initialized(create_keccak_permutation_indices_table::<F>(id))
            }
            TableType::XorSpecialIota => {
                LookupWrapper::Initialized(create_xor_special_keccak_iota_table::<F>(id))
            }
            TableType::AndN => LookupWrapper::Initialized(create_andn_table::<F>(id)),
            TableType::RotL => LookupWrapper::Initialized(create_rotl_table::<F>(id)),
            a @ _ => {
                todo!("Support {:?}", a);
            }
        }
    }

    pub fn get_table_from_id(id: u32) -> Self {
        if id as usize >= TOTAL_NUM_OF_TABLES {
            panic!("Unknown table id {}", id);
        } else {
            unsafe { std::mem::transmute(id) }
        }
    }
}

#[inline(always)]
pub(crate) fn first_key_index_gen_fn<F: PrimeField>(keys: &[F]) -> usize {
    keys[0].as_u32_reduced() as usize
}

#[inline(always)]
fn u8_chunks_index_gen_fn<F: PrimeField, const N: usize>(keys: &[F; N]) -> usize {
    let a = keys[0].as_u32_reduced();
    let b = keys[1].as_u32_reduced();

    assert!(a <= u8::MAX as u32);
    assert!(b <= u8::MAX as u32);

    index_for_binary_key(a, b)
}

#[inline(always)]
fn bit_chunks_slice_index_gen_fn<F: PrimeField, const WIDTH: usize>(keys: &[F]) -> usize {
    assert!(keys.len() >= 2);
    let a = keys[0].as_u32_reduced();
    let b = keys[1].as_u32_reduced();

    assert!(a < 1u32 << WIDTH);
    assert!(b < 1u32 << WIDTH);

    index_for_binary_key_for_width::<WIDTH>(a, b)
}

#[inline(always)]
fn bit_chunks_index_gen_fn<F: PrimeField, const N: usize, const WIDTH: usize>(
    keys: &[F; N],
) -> usize {
    let a = keys[0].as_u32_reduced();
    let b = keys[1].as_u32_reduced();

    assert!(a < 1u32 << WIDTH);
    assert!(b < 1u32 << WIDTH);

    index_for_binary_key_for_width::<WIDTH>(a, b)
}

fn index_for_binary_key(a: u32, b: u32) -> usize {
    ((a << 8) | b) as usize
}

fn index_for_binary_key_for_width<const WIDTH: usize>(a: u32, b: u32) -> usize {
    ((a << WIDTH) | b) as usize
}

// we make it so that index in the table is just (key0 << 8) || key1
pub fn key_binary_generation<F: PrimeField, const N: usize>() -> Vec<[F; N]> {
    let mut keys = Vec::with_capacity(1 << 16);
    for a in 0..(1u64 << 8) {
        for b in 0..(1u64 << 8) {
            let mut key = [F::ZERO; N];
            key[0] = F::from_u32_unchecked(a as u32);
            key[1] = F::from_u32_unchecked(b as u32);
            keys.push(key);
        }
    }

    keys
}

// we make it so that index in the table is just (key0 << WIDTH) || key1
pub fn key_binary_generation_for_width<F: PrimeField, const N: usize, const WIDTH: usize>(
) -> Vec<[F; N]> {
    let len = 1 << (WIDTH * 2);
    let mut keys = Vec::with_capacity(len);
    if WIDTH < 10 {
        for a in 0..(1u64 << WIDTH) {
            for b in 0..(1u64 << WIDTH) {
                let mut key = [F::ZERO; N];
                key[0] = F::from_u32_unchecked(a as u32);
                key[1] = F::from_u32_unchecked(b as u32);
                keys.push(key);
            }
        }
    } else {
        (0..len)
            .into_par_iter()
            .map(|i| {
                let i = i as u32;
                let a = i >> WIDTH;
                let b = i & ((1u32 << WIDTH) - 1);
                let mut key = [F::ZERO; N];
                key[0] = F::from_u32_unchecked(a);
                key[1] = F::from_u32_unchecked(b);
                key
            })
            .collect_into_vec(&mut keys);
    }
    assert_eq!(keys.len(), len);

    keys
}

pub fn key_for_continuous_log2_range<F: PrimeField, const N: usize>(log2: usize) -> Vec<[F; N]> {
    let keys = key_for_continuous_range((1u64 << log2) - 1);
    assert_eq!(keys.len(), 1 << log2);

    keys
}

pub fn key_for_continuous_range<F: PrimeField, const N: usize>(
    max_value_inclusive: u64,
) -> Vec<[F; N]> {
    let len = max_value_inclusive as usize + 1;
    let mut keys = Vec::with_capacity(len);
    if max_value_inclusive < (1 << 20) {
        for a in 0u64..=max_value_inclusive {
            let mut key = [F::ZERO; N];
            key[0] = F::from_u64_with_reduction(a);
            keys.push(key);
        }
    } else {
        (0..len)
            .into_par_iter()
            .map(|a| {
                let mut key = [F::ZERO; N];
                key[0] = F::from_u64_with_reduction(a as u64);
                key
            })
            .collect_into_vec(&mut keys);
    };
    assert_eq!(keys.len(), len);

    keys
}

pub fn key_get_bit<F: PrimeField, const N: usize>() -> Vec<SmallVec<[F; N]>> {
    let keys = (0..=u16::MAX)
        .flat_map(|a| {
            (0..16).map(move |b| {
                smallvec::smallvec![
                    F::from_u32_unchecked(a as u32),
                    F::from_u32_unchecked(b as u32)
                ]
            })
        })
        .collect();

    keys
}

/// Manages multiple lookup tables.
#[derive(Clone, Debug)]
pub struct TableDriver<F: PrimeField> {
    pub tables: [LookupWrapper<F>; TABLE_TYPES_UPPER_BOUNDS],
    offsets_for_multiplicities: [usize; TABLE_TYPES_UPPER_BOUNDS],
    pub total_tables_len: usize,
}

impl<F: PrimeField> TableDriver<F> {
    pub fn new() -> Self {
        TableDriver {
            tables: std::array::from_fn(|_| LookupWrapper::Uninitialized),
            offsets_for_multiplicities: [0usize; TABLE_TYPES_UPPER_BOUNDS],
            total_tables_len: 0,
        }
    }

    fn update_table_offsets(&mut self) {
        let mut offset = 0;
        for (dst, src) in self
            .offsets_for_multiplicities
            .iter_mut()
            .zip(self.tables.iter())
        {
            *dst = offset;
            offset += src.get_size();
        }
        assert_eq!(offset, self.total_tables_len);
    }

    pub fn add_table_with_content(&mut self, table_type: TableType, table: LookupWrapper<F>) {
        match &table {
            LookupWrapper::Uninitialized => {
                panic!(
                    "Trying to add initialized wrapper for table type {:?}",
                    table_type
                );
            }
            _ => {}
        }
        let id = table.get_table_id() as usize;
        assert_eq!(id, table_type.to_table_id() as usize);
        if self.tables[id].is_initialized() {
            // duplicate init, fine
            return;
        }
        let table_size = table.get_size();
        self.tables[id] = table;
        self.total_tables_len += table_size;
        self.update_table_offsets();
    }

    pub fn max_table_width(&self) -> usize {
        self.tables.iter().map(|el| el.width()).max().unwrap_or(0)
    }

    pub fn materialize_table<const TOTAL_WIDTH: usize>(&mut self, table_type: TableType) {
        static CACHE: LazyLock<Mutex<TypeMap>> = LazyLock::new(|| Mutex::new(TypeMap::default()));
        let mut guard = CACHE.lock().unwrap();
        let map = guard
            .entry()
            .or_insert_with(HashMap::<(TableType, usize), LookupWrapper<F>>::new);
        let wrapper = map
            .entry((table_type, TOTAL_WIDTH))
            .or_insert_with(|| table_type.generate_table::<F, TOTAL_WIDTH>());
        let table = wrapper.clone();
        self.add_table_with_content(table_type, table);
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup_values<const N: usize>(&self, keys: &[F], id: u32) -> [F; N] {
        let table = &self.tables[id as usize];
        assert!(
            table.is_initialized(),
            "table with id = {:?} is not initialized",
            id
        );
        let values = table.lookup_value(keys);

        values
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup_values_and_get_absolute_index<const N: usize>(
        &self,
        keys: &[F],
        id: u32,
    ) -> (usize, [F; N]) {
        let offset = self.get_start_table_offset(id);
        let table = &self.tables[id as usize];
        assert!(
            table.is_initialized(),
            "table with id = {:?} is not initialized",
            id
        );
        let (mut index, values) = table.lookup_values_and_get_index(keys);
        index += offset;

        (index, values)
    }

    #[track_caller]
    #[inline(always)]
    pub fn enforce_values_and_get_absolute_index<const N: usize>(
        &self,
        keys: &[F; N],
        id: u32,
    ) -> usize {
        let offset = self.get_start_table_offset(id);
        let table = &self.tables[id as usize];
        assert!(
            table.is_initialized(),
            "table with id = {:?} is not initialized",
            id
        );
        let mut index = table.lookup_row(keys);
        index += offset;

        index
    }

    // // #[inline(always)]
    // // pub fn lookup_row(&self, row: &[F], id: u32) -> bool {
    // //     self.tables[id as usize].lookup_row(row).is_some()
    // // }

    #[inline(always)]
    pub fn get_start_table_offset(&self, id: u32) -> usize {
        self.offsets_for_multiplicities[id as usize]
    }

    pub fn table_starts_offsets(&self) -> [usize; TABLE_TYPES_UPPER_BOUNDS] {
        self.offsets_for_multiplicities
    }

    // #[inline(always)]
    // pub fn get_table(&self, table_type: TableType) -> &LookupWrapper<F> {
    //     &self.tables[table_type.to_table_id() as usize]
    // }

    // #[inline(always)]
    // pub fn get_table_by_id(&self, id: u32) -> &LookupWrapper<F> {
    //     &self.tables[id as usize]
    // }

    pub fn dump_tables(
        &self,
        total_width_including_id: usize,
    ) -> Vec<ArrayVec<F, MAX_TABLE_WIDTH>> {
        let max_width_without_id = self.max_table_width();
        if max_width_without_id >= total_width_including_id {
            for t in self.tables.iter() {
                if let LookupWrapper::Initialized(t) = t {
                    println!("Table `{}` has width {} (without ID)", &t.name, t.width());
                }
            }
            panic!("trying to dump tables with max width {} (without ID) into total of {} columns (with ID)", max_width_without_id, total_width_including_id);
        }
        let mut result = Vec::with_capacity(self.total_tables_len);
        for table in self.tables.iter() {
            if table.get_size() == 0 {
                continue;
            }
            let id = table.get_table_id();
            table.dump_into(&mut result, Some(id), total_width_including_id);
        }

        result
    }
}

// #[cfg(test)]
// mod test {
//     use field::Mersenne31Field;
//     use rand::Rng;
//     use rand::SeedableRng;
//     use std::collections::BTreeMap;
//     use std::collections::HashMap;

//     use super::*;

//     #[test]
//     fn bench_btree_lookup() {
//         let table = TableType::Xor.generate_table::<Mersenne31Field>();
//         let num_queries = 1 << 23;
//         let mut rng = rand::rngs::StdRng::seed_from_u64(42);
//         let queries: Vec<[Mersenne31Field; 2]> = (0..num_queries)
//             .map(|_| {
//                 let a: u8 = rng.random();
//                 let b: u8 = rng.random();

//                 [Mersenne31Field(a as u32), Mersenne31Field(b as u32)]
//             })
//             .collect();

//         let current_time = std::time::Instant::now();
//         for input in queries.iter() {
//             let _ = table.lookup_value::<1>(input);
//         }
//         dbg!(current_time.elapsed());

//         // simulate as hashmap
//         let mut map = HashMap::new();
//         let LookupWrapper::Dimensional3(table) = &table else {
//             unreachable!()
//         };

//         for (k, v) in table.lookup_data.iter() {
//             map.insert(k.clone(), v.clone());
//         }

//         let hashmap_time = std::time::Instant::now();
//         for input in queries.iter() {
//             let key = LookupKey::<Mersenne31Field, 3>::from_keys(input);
//             let _ = map.get(&key);
//         }
//         dbg!(hashmap_time.elapsed());

//         // simulate as btree without indirection
//         let mut btree = BTreeMap::new();

//         for (k, v) in table.lookup_data.iter() {
//             btree.insert(k.clone(), v.clone());
//         }

//         let btree_time = std::time::Instant::now();
//         for input in queries.iter() {
//             let key = LookupKey::<Mersenne31Field, 3>::from_keys(input);
//             let _ = btree.get(&key);
//         }
//         dbg!(btree_time.elapsed());

//         // simulate as ordered vector
//         let mut ordered_vector = Vec::new();

//         for (k, v) in table.lookup_data.iter() {
//             ordered_vector.push((k.clone(), v.clone()));
//         }

//         ordered_vector.sort_by(|a, b| a.0.cmp(&b.0));

//         let vec_time = std::time::Instant::now();
//         for input in queries.iter() {
//             let key = LookupKey::<Mersenne31Field, 3>::from_keys(input);
//             let _ = ordered_vector.binary_search_by_key(&key, |(a, _)| a.clone());
//         }
//         dbg!(vec_time.elapsed());
//     }
// }
