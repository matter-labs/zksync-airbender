use core::panic;
use derivative::Derivative;
use field::PrimeField;
use smallvec::SmallVec;
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

pub use super::definitions::TableType;

const TOTAL_NUM_OF_TABLES: usize = TableType::DynamicPlaceholder as u32 as usize;

// NOTE: we follow the convention to pass keys and return values in a padded form,
// so it's always fixed size, but "unused" values are 0s

// keys -> index in table and values
pub type PureTableGenerationFn<F: PrimeField, const N: usize> = fn(&[F; N]) -> (usize, [F; N]);
pub type TableGenerationClosure<F: PrimeField, const N: usize> = std::sync::Arc<
    dyn Fn(&[F; N]) -> (usize, [F; N])
        + 'static
        + Send
        + Sync
        + std::panic::UnwindSafe
        + std::panic::RefUnwindSafe,
>;

#[derive(Derivative)]
#[derivative(Clone)]
pub enum ValueLookupFn<F: PrimeField, const N: usize> {
    None,
    Pure(fn(&[F]) -> [F; N]),
    ReuseGenerationFn(PureTableGenerationFn<F, N>),
    Closure(TableGenerationClosure<F, N>),
}

#[derive(Derivative)]
#[derivative(Clone)]
pub enum IndexLookupFn<F: PrimeField, const N: usize> {
    None,
    Pure(fn(&[F; N]) -> usize),
    ReuseGenerationFn(PureTableGenerationFn<F, N>),
    ReuseGenerationClosure(TableGenerationClosure<F, N>),
    Closure(std::sync::Arc<dyn Fn(&[F; N]) -> usize + 'static + Send + Sync>),
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct LookupTable<F: PrimeField, const N: usize> {
    pub name: String,

    // NOTE: for small fields and not too large N hashmaps are the most efficient here

    // to lookup value from key
    #[derivative(Debug = "ignore")]
    pub lookup_data: HashMap<LookupKey<F, N>, LookupValue<F, N>>,
    // to lookup table index from full row
    #[derivative(Debug = "ignore")]
    pub content_data: HashMap<DataKey<F, N>, usize>,
    // for setup - plain content of the table
    #[derivative(Debug = "ignore")]
    pub data: Vec<[F; N]>,
    #[derivative(Debug = "ignore")]
    pub quick_value_lookup_fn: ValueLookupFn<F, N>,
    #[derivative(Debug = "ignore")]
    pub quick_index_lookup_fn: IndexLookupFn<F, N>,

    pub num_key_columns: usize,
    pub num_value_columns: usize,

    pub id: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LookupKey<F: PrimeField, const N: usize>([F; N]);

pub type LookupValue<F, const N: usize> = LookupKey<F, N>;

impl<F: PrimeField, const N: usize> LookupKey<F, N> {
    fn from_keys(keys: &[F]) -> Self {
        let mut new = [F::ZERO; N];
        new[..keys.len()].copy_from_slice(keys);

        Self(new)
    }
}

impl<F: PrimeField, const N: usize> PartialOrd for LookupKey<F, N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            match a.as_u64_reduced().cmp(&b.as_u64_reduced()) {
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
impl<F: PrimeField, const N: usize> Ord for LookupKey<F, N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        debug_assert_eq!(self.0.len(), other.0.len());
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            match a.as_u64_reduced().cmp(&b.as_u64_reduced()) {
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DataKey<F: PrimeField, const N: usize>([F; N]);

impl<F: PrimeField, const N: usize> PartialOrd for DataKey<F, N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            match a.as_u64_reduced().cmp(&b.as_u64_reduced()) {
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
impl<F: PrimeField, const N: usize> Ord for DataKey<F, N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        debug_assert_eq!(self.0.len(), other.0.len());
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            match a.as_u64_reduced().cmp(&b.as_u64_reduced()) {
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

impl<F: PrimeField, const N: usize> LookupTable<F, N> {
    fn check_well_formed(data: &[[F; N]]) -> bool {
        // just use hash table to check that entries are unique
        let mut tmp = HashSet::new();
        for el in data.iter() {
            let is_unique = tmp.insert(*el);
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

    pub(crate) fn create_table_from_key_and_pure_generation_fn(
        keys: &Vec<[F; N]>,
        name: String,
        num_key_columns: usize,
        table_gen_func: PureTableGenerationFn<F, N>,
        index_gen_fn: Option<fn(&[F; N]) -> usize>,
        id: u32,
    ) -> Self {
        assert!(num_key_columns <= N);
        let num_value_columns = N - num_key_columns;

        let mut content = Vec::with_capacity(keys.len());
        for key in keys.iter() {
            let (_index, values) = table_gen_func(&key);
            let mut row = [F::ZERO; N];
            row[..num_key_columns].copy_from_slice(&key[..num_key_columns]);
            row[num_key_columns..].copy_from_slice(&values[..num_value_columns]);
            content.push(row);
        }

        let (lookup_data, content_data) =
            Self::compute_default_lookup_impls(&content, num_key_columns);

        let index_gen_fn = if let Some(index_gen_fn) = index_gen_fn {
            IndexLookupFn::Pure(index_gen_fn)
        } else {
            IndexLookupFn::ReuseGenerationFn(table_gen_func)
        };

        Self {
            name,
            lookup_data,
            content_data,
            data: content,
            quick_value_lookup_fn: ValueLookupFn::ReuseGenerationFn(table_gen_func),
            quick_index_lookup_fn: index_gen_fn,
            num_key_columns,
            num_value_columns,
            id,
        }
    }

    pub(crate) fn create_table_from_key_and_key_generation_closure<
        FN: Fn(&[F; N]) -> (usize, [F; N])
            + 'static
            + Send
            + Sync
            + Clone
            + std::panic::UnwindSafe
            + std::panic::RefUnwindSafe,
    >(
        keys: &Vec<[F; N]>,
        name: String,
        num_key_columns: usize,
        table_gen_closure: FN,
        index_gen_fn: Option<fn(&[F; N]) -> usize>,
        id: u32,
    ) -> Self {
        assert!(num_key_columns <= N);
        let num_value_columns = N - num_key_columns;

        let mut content = Vec::with_capacity(keys.len());
        for key in keys.iter() {
            let (_index, values) = table_gen_closure(&key);
            let mut row = [F::ZERO; N];
            row[..num_key_columns].copy_from_slice(&key[..num_key_columns]);
            row[num_key_columns..].copy_from_slice(&values[..num_value_columns]);
            content.push(row);
        }

        let (lookup_data, content_data) =
            Self::compute_default_lookup_impls(&content, num_key_columns);

        let index_gen_fn = if let Some(index_gen_fn) = index_gen_fn {
            IndexLookupFn::Pure(index_gen_fn)
        } else {
            IndexLookupFn::ReuseGenerationClosure(Arc::new(table_gen_closure.clone()))
        };

        Self {
            name,
            lookup_data,
            content_data,
            data: content,
            quick_value_lookup_fn: ValueLookupFn::Closure(Arc::new(table_gen_closure)),
            quick_index_lookup_fn: index_gen_fn,
            num_key_columns,
            num_value_columns,
            id,
        }
    }

    fn compute_default_lookup_impls(
        data: &Vec<[F; N]>,
        num_key_columns: usize,
    ) -> (
        HashMap<LookupKey<F, N>, LookupKey<F, N>>,
        HashMap<DataKey<F, N>, usize>,
    ) {
        let is_well_formed = Self::check_well_formed(&data);
        assert!(is_well_formed);
        let lookup_data: HashMap<LookupKey<F, N>, LookupKey<F, N>> =
            Self::compute_lookup_data(data, num_key_columns);
        let mut content_data: HashMap<DataKey<F, N>, usize> = HashMap::new();
        for (idx, el) in data.iter().enumerate() {
            content_data.insert(DataKey(*el), idx);
        }

        (lookup_data, content_data)
    }

    /// Splits data elements into key, value.
    /// We treat first num_key_columns elements from each data item
    /// as key, and the rest as value.
    fn compute_lookup_data(
        data: &Vec<[F; N]>,
        num_key_columns: usize,
    ) -> HashMap<LookupKey<F, N>, LookupValue<F, N>> {
        assert!(num_key_columns <= N);
        let mut result = HashMap::new();
        for row in data.iter() {
            let key = LookupKey::from_keys(&row[..num_key_columns]);
            let value = LookupValue::from_keys(&row[num_key_columns..]);
            let existing = result.insert(key, value);
            assert!(existing.is_none(), "Can't compute lookup cache if using only {} first columns out of {} as logical key", num_key_columns, N);
        }

        result
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup_value<const VALUES: usize>(&self, keys: &[F]) -> [F; VALUES] {
        assert!(keys.len() < N);
        assert!(VALUES < N);
        assert_eq!(keys.len(), N - VALUES);
        // NOTE that lookup function return padded values in generation functions
        match &self.quick_value_lookup_fn {
            ValueLookupFn::None => {
                let keys = LookupKey::from_keys(keys);
                let Some(value) = self.lookup_data.get(&keys).cloned() else {
                    panic!(
                        "There is no value for key {:?} for table {}",
                        keys,
                        self.name()
                    );
                };

                std::array::from_fn(|i| value.0[i])
            }
            ValueLookupFn::Pure(..) => {
                unimplemented!()
            }
            ValueLookupFn::ReuseGenerationFn(gen_fn) => {
                let mut input = [F::ZERO; N];
                input[..keys.len()].copy_from_slice(keys);
                let (_, values) = (gen_fn)(&input);

                std::array::from_fn(|i| values[i])
            }
            ValueLookupFn::Closure(gen_closure) => {
                let mut input = [F::ZERO; N];
                input[..keys.len()].copy_from_slice(keys);
                let (_, values) = (gen_closure)(&input);

                std::array::from_fn(|i| values[i])
            }
        }
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup_values_and_get_index<const VALUES: usize>(
        &self,
        keys: &[F],
    ) -> (usize, [F; VALUES]) {
        assert!(keys.len() < N);
        assert!(VALUES < N);
        assert_eq!(keys.len(), N - VALUES);
        // NOTE that lookup function return padded values in generation functions
        match &self.quick_value_lookup_fn {
            ValueLookupFn::None => {
                let keys = LookupKey::from_keys(keys);
                let Some(_value) = self.lookup_data.get(&keys).cloned() else {
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
                let mut input = [F::ZERO; N];
                input[..keys.len()].copy_from_slice(keys);
                let (index, values) = (gen_fn)(&input);

                (index, std::array::from_fn(|i| values[i]))
            }
            ValueLookupFn::Closure(gen_closure) => {
                let mut input = [F::ZERO; N];
                input[..keys.len()].copy_from_slice(keys);
                let (index, values) = (gen_closure)(&input);

                (index, std::array::from_fn(|i| values[i]))
            }
        }
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup_row(&self, key: &[F]) -> usize {
        assert_eq!(key.len(), N);
        match &self.quick_index_lookup_fn {
            IndexLookupFn::None => {
                let keys = unsafe { key.as_ptr().cast::<[F; N]>().read() };
                let key = DataKey(keys);
                self.content_data.get(&key).copied().unwrap()
            }
            IndexLookupFn::Pure(index_fn) => {
                let keys = unsafe { key.as_ptr().cast::<[F; N]>().as_ref_unchecked() };
                let index = (index_fn)(&keys);
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
                let keys = unsafe { key.as_ptr().cast::<[F; N]>().as_ref_unchecked() };
                // NOTE: generation functions do not use padding places, so we can feed as-is
                let (index, values) = (gen_fn)(keys);
                // can self-check
                assert_eq!(
                    &values[..self.num_value_columns],
                    &key[self.num_key_columns..]
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
                let keys = unsafe { key.as_ptr().cast::<[F; N]>().as_ref_unchecked() };
                // NOTE: generation functions do not use padding places, so we can feed as-is
                let (index, values) = (gen_closure)(&keys);
                // can self-check
                assert_eq!(
                    &values[..self.num_value_columns],
                    &key[self.num_key_columns..]
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

    pub fn data_at_row(&self, row: usize) -> &[F] {
        &self.data[row][..]
    }

    pub fn dump_into<const M: usize>(&self, dst: &mut Vec<[F; M]>, id: Option<u32>) {
        let required_len = N + id.is_some() as usize;
        assert!(M >= required_len);
        for row in self.data.iter() {
            let mut assembled_row = [F::ZERO; M];
            assembled_row[..N].copy_from_slice(&row[..]);
            if let Some(id) = id {
                assembled_row[N] = F::from_u64_unchecked(id as u64);
            }
            dst.push(assembled_row);
        }
    }

    pub fn dump_limited_columns<const M: usize>(&self, dst: &mut Vec<[F; M]>) {
        assert!(M <= N);
        for row in self.data.iter() {
            let mut assembled_row = [F::ZERO; M];
            assembled_row[..].copy_from_slice(&row[..M]);
            dst.push(assembled_row);
        }
    }
}

#[derive(Clone, Debug)]
pub enum LookupWrapper<F: PrimeField> {
    Uninitialized,
    Dimensional1(LookupTable<F, 1>),
    Dimensional2(LookupTable<F, 2>),
    Dimensional3(LookupTable<F, 3>),
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
            Self::Dimensional1(..) => 1,
            Self::Dimensional2(..) => 2,
            Self::Dimensional3(..) => 3,
            Self::Uninitialized => 0,
        }
    }

    pub fn get_table_id(&self) -> u32 {
        match self {
            LookupWrapper::Dimensional1(table) => table.id,
            LookupWrapper::Dimensional2(table) => table.id,
            LookupWrapper::Dimensional3(table) => table.id,
            Self::Uninitialized => unreachable!(),
        }
    }

    #[track_caller]
    #[inline]
    pub fn lookup_value<const VALUES: usize>(&self, keys: &[F]) -> [F; VALUES] {
        match self {
            Self::Dimensional1(inner) => inner.lookup_value(keys),
            Self::Dimensional2(inner) => inner.lookup_value(keys),
            Self::Dimensional3(inner) => inner.lookup_value(keys),
            Self::Uninitialized => unreachable!(),
        }
    }

    #[track_caller]
    #[inline]
    pub fn lookup_values_and_get_index<const VALUES: usize>(
        &self,
        keys: &[F],
    ) -> (usize, [F; VALUES]) {
        match self {
            Self::Dimensional1(inner) => inner.lookup_values_and_get_index(keys),
            Self::Dimensional2(inner) => inner.lookup_values_and_get_index(keys),
            Self::Dimensional3(inner) => inner.lookup_values_and_get_index(keys),
            Self::Uninitialized => unreachable!(),
        }
    }

    #[track_caller]
    #[inline]
    pub fn lookup_row(&self, row: &[F]) -> usize {
        match self {
            Self::Dimensional1(inner) => inner.lookup_row(row),
            Self::Dimensional2(inner) => inner.lookup_row(row),
            Self::Dimensional3(inner) => inner.lookup_row(row),
            Self::Uninitialized => {
                panic!("Trying to lookup into uninitialized table wrapper");
            }
        }
    }

    pub fn get_size(&self) -> usize {
        match self {
            Self::Dimensional1(inner) => inner.table_size(),
            Self::Dimensional2(inner) => inner.table_size(),
            Self::Dimensional3(inner) => inner.table_size(),
            Self::Uninitialized => 0,
        }
    }

    pub fn data_at_row(&self, row: usize) -> &[F] {
        match self {
            Self::Dimensional1(inner) => inner.data_at_row(row),
            Self::Dimensional2(inner) => inner.data_at_row(row),
            Self::Dimensional3(inner) => inner.data_at_row(row),
            Self::Uninitialized => &[],
        }
    }

    pub fn dump_into<const N: usize>(&self, dst: &mut Vec<[F; N]>, id: Option<u32>) {
        match self {
            Self::Dimensional1(inner) => inner.dump_into::<N>(dst, id),
            Self::Dimensional2(inner) => inner.dump_into::<N>(dst, id),
            Self::Dimensional3(inner) => inner.dump_into::<N>(dst, id),
            Self::Uninitialized => {}
        }
    }

    pub fn dump_limited_columns<const N: usize>(&self, dst: &mut Vec<[F; N]>) {
        match self {
            Self::Dimensional1(inner) => inner.dump_limited_columns::<N>(dst),
            Self::Dimensional2(inner) => inner.dump_limited_columns::<N>(dst),
            Self::Dimensional3(inner) => inner.dump_limited_columns::<N>(dst),
            Self::Uninitialized => {}
        }
    }
}

// -------------------------------------Tables Realization------------------------------------
// -------------------------------------------------------------------------------------------

impl quote::ToTokens for TableType {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        use quote::quote;
        let stream = match self {
            TableType::And => quote! { TableType::And },
            TableType::Xor => quote! { TableType::Xor },
            TableType::Or => quote! { TableType::Or },
            TableType::RangeCheckSmall => quote! { TableType::RangeCheckSmall },
            TableType::RangeCheckLarge => quote! { TableType::RangeCheckLarge },
            TableType::PowersOf2 => quote! { TableType::PowersOf2 },
            TableType::OpTypeBitmask => quote! { TableType::OpTypeBitmask },
            TableType::InsnEncodingChecker => quote! { TableType::InsnEncodingChecker },
            TableType::CsrBitmask => quote! { TableType::CsrBitmask },
            TableType::ZeroEntry => quote! { TableType::ZeroEntry },
            TableType::AndNot => quote! { TableType::AndNot },
            TableType::QuickDecodeDecompositionCheck4x4x4 => {
                quote! { TableType::QuickDecodeDecompositionCheck4x4x4 }
            }
            TableType::QuickDecodeDecompositionCheck7x3x6 => {
                quote! { TableType::QuickDecodeDecompositionCheck7x3x6 }
            }
            TableType::MRetProcessLow => quote! { TableType::MRetProcessLow },
            TableType::MRetClearHigh => quote! { TableType::MRetClearHigh },
            TableType::TrapProcessLow => quote! { TableType::TrapProcessLow },
            TableType::U16GetSignAndHighByte => quote! { TableType::U16GetSignAndHighByte },
            TableType::JumpCleanupOffset => quote! { TableType::JumpCleanupOffset },
            TableType::MemoryOffsetGetBits => quote! { TableType::MemoryOffsetGetBits },
            TableType::MemoryLoadGetSigns => quote! { TableType::MemoryLoadGetSigns },
            TableType::SRASignFiller => quote! { TableType::SRASignFiller },
            TableType::ConditionalOpAllConditionsResolver => {
                quote! { TableType::ConditionalOpAllConditionsResolver }
            }
            TableType::RomAddressSpaceSeparator => quote! { TableType::RomAddressSpaceSeparator },
            TableType::RomRead => quote! { TableType::RomRead },
            TableType::SpecialCSRProperties => quote! { TableType::SpecialCSRProperties },
            TableType::Xor3 => quote! { TableType::Xor3 },
            TableType::Xor4 => quote! { TableType::Xor4 },
            TableType::Xor7 => quote! { TableType::Xor7 },
            TableType::Xor9 => quote! { TableType::Xor9 },
            TableType::Xor12 => quote! { TableType::Xor12 },
            TableType::U16SplitAsBytes => quote! { TableType::U16SplitAsBytes },
            TableType::RangeCheck9x9 => quote! { TableType::RangeCheck9x9 },
            TableType::RangeCheck10x10 => quote! { TableType::RangeCheck10x10 },
            TableType::RangeCheck11 => quote! { TableType::RangeCheck11 },
            TableType::RangeCheck12 => quote! { TableType::RangeCheck12 },
            TableType::RangeCheck13 => quote! { TableType::RangeCheck13 },
            TableType::ShiftImplementation => quote! { TableType::ShiftImplementation },
            TableType::U16SelectByteAndGetByteSign => {
                quote! { TableType::U16SelectByteAndGetByteSign }
            }
            TableType::ConditionalOpUnsignedConditionsResolver => {
                todo!()
            }
            TableType::StoreByteSourceContribution => {
                quote! { TableType::StoreByteSourceContribution }
            }
            TableType::StoreByteExistingContribution => {
                quote! { TableType::StoreByteExistingContribution }
            }
            TableType::ExtendLoadedValue => quote! { TableType::ExtendLoadedValue },
            TableType::TruncateShift => quote! { TableType::TruncateShift },
            TableType::DynamicPlaceholder => {
                unimplemented!("should not appear in final circuits")
            }
        };

        tokens.extend(stream);
    }
}

impl TableType {
    pub fn to_table_id(&self) -> u32 {
        *self as u32
    }
}

impl TableType {
    pub fn generate_table<F: PrimeField>(self) -> LookupWrapper<F> {
        let id = self.to_table_id();
        match self {
            TableType::And => LookupWrapper::Dimensional3(create_and_table(id)),
            TableType::Xor => LookupWrapper::Dimensional3(create_xor_table::<F, 8>(id)),
            TableType::Or => LookupWrapper::Dimensional3(create_or_table(id)),
            TableType::RangeCheckSmall => LookupWrapper::Dimensional3(
                create_formal_width_3_range_check_table_for_two_tuple::<F, 8>(id),
            ),
            TableType::RangeCheckLarge => {
                LookupWrapper::Dimensional1(create_range_check_table::<F, 16>(id))
            }
            TableType::PowersOf2 => LookupWrapper::Dimensional3(create_pow2_table::<F, 5>(id)),
            TableType::OpTypeBitmask => {
                panic!("Machine must defined it's own way to create supporting decoder table")
            }
            TableType::InsnEncodingChecker => {
                panic!("deprecated")
            }
            TableType::CsrBitmask => {
                panic!("Machine must defined it's own way to define CSR support")
                // LookupWrapper::Dimensional3(create_csr_bitmask_table(id))
            }
            TableType::ZeroEntry => LookupWrapper::Dimensional3(create_zero_entry_table(id)),
            TableType::AndNot => LookupWrapper::Dimensional3(create_and_not_table(id)),
            TableType::QuickDecodeDecompositionCheck4x4x4 => {
                LookupWrapper::Dimensional3(create_quick_decoder_decomposition_table_4x4x4(id))
            }
            TableType::QuickDecodeDecompositionCheck7x3x6 => {
                LookupWrapper::Dimensional3(create_quick_decoder_decomposition_table_7x3x6(id))
            }
            TableType::MRetProcessLow => {
                unimplemented!()
                // LookupWrapper::Dimensional3(create_mret_process_low_table(id))
            }
            TableType::MRetClearHigh => {
                unimplemented!()
                // LookupWrapper::Dimensional3(create_mret_clear_high_table(id))
            }
            TableType::TrapProcessLow => {
                unimplemented!()
                // LookupWrapper::Dimensional3(create_trap_process_low_table(id))
            }
            TableType::U16GetSignAndHighByte => {
                LookupWrapper::Dimensional3(create_u16_get_sign_and_high_byte_table(id))
            }
            TableType::JumpCleanupOffset => {
                LookupWrapper::Dimensional3(create_jump_cleanup_offset_table(id))
            }
            TableType::MemoryOffsetGetBits => {
                LookupWrapper::Dimensional3(create_memory_offset_lowest_bits_table(id))
            }
            TableType::MemoryLoadGetSigns => {
                LookupWrapper::Dimensional3(create_memory_load_signs_table(id))
            }
            TableType::SRASignFiller => {
                LookupWrapper::Dimensional3(create_sra_sign_filler_table(id))
            }
            TableType::ConditionalOpAllConditionsResolver => {
                LookupWrapper::Dimensional3(create_conditional_op_resolution_table(id))
            }
            TableType::RomAddressSpaceSeparator => {
                unimplemented!("must manually generate a table to customize number of bits");
                // LookupWrapper::Dimensional3(create_rom_separator_table::<
                //     F,
                //     ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
                // >(id))
            }
            TableType::SpecialCSRProperties => {
                unimplemented!("must be created in a special manner");
            }
            TableType::Xor3 => LookupWrapper::Dimensional3(create_xor_table::<F, 3>(id)),
            TableType::Xor4 => LookupWrapper::Dimensional3(create_xor_table::<F, 4>(id)),
            TableType::Xor7 => LookupWrapper::Dimensional3(create_xor_table::<F, 7>(id)),
            TableType::Xor9 => LookupWrapper::Dimensional3(create_xor_table::<F, 9>(id)),
            TableType::Xor12 => LookupWrapper::Dimensional3(create_xor_table::<F, 12>(id)),
            TableType::U16SplitAsBytes => {
                LookupWrapper::Dimensional3(create_u16_split_into_bytes_table(id))
            }
            TableType::RangeCheck9x9 => LookupWrapper::Dimensional3(
                create_formal_width_3_range_check_table_for_two_tuple::<F, 9>(id),
            ),
            TableType::RangeCheck10x10 => LookupWrapper::Dimensional3(
                create_formal_width_3_range_check_table_for_two_tuple::<F, 10>(id),
            ),
            TableType::RangeCheck11 => LookupWrapper::Dimensional3(
                create_formal_width_3_range_check_table_for_single_entry::<F, 11>(id),
            ),
            TableType::RangeCheck12 => LookupWrapper::Dimensional3(
                create_formal_width_3_range_check_table_for_single_entry::<F, 12>(id),
            ),
            TableType::RangeCheck13 => LookupWrapper::Dimensional3(
                create_formal_width_3_range_check_table_for_single_entry::<F, 13>(id),
            ),
            TableType::ShiftImplementation => {
                LookupWrapper::Dimensional3(create_shift_implementation_table::<F>(id))
            }
            TableType::U16SelectByteAndGetByteSign => {
                LookupWrapper::Dimensional3(create_select_byte_and_get_sign_table::<F>(id))
            }
            TableType::ExtendLoadedValue => {
                LookupWrapper::Dimensional3(create_mem_load_extend_table::<F>(id))
            }
            TableType::StoreByteSourceContribution => {
                LookupWrapper::Dimensional3(create_store_byte_source_contribution_table::<F>(id))
            }
            TableType::StoreByteExistingContribution => {
                LookupWrapper::Dimensional3(create_store_byte_existing_contribution_table::<F>(id))
            }
            TableType::TruncateShift => {
                LookupWrapper::Dimensional3(create_truncate_shift_amount_table::<F>(id))
            }

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
pub(crate) fn first_key_index_gen_fn<F: PrimeField, const N: usize>(keys: &[F; N]) -> usize {
    keys[0].as_u64_reduced() as usize
}

#[inline(always)]
fn u8_chunks_index_gen_fn<F: PrimeField, const N: usize>(keys: &[F; N]) -> usize {
    let a = keys[0].as_u64_reduced();
    let b = keys[1].as_u64_reduced();

    assert!(a <= u8::MAX as u64);
    assert!(b <= u8::MAX as u64);

    index_for_binary_key(a, b)
}

#[inline(always)]
fn bit_chunks_index_gen_fn<F: PrimeField, const N: usize, const WIDTH: usize>(
    keys: &[F; N],
) -> usize {
    let a = keys[0].as_u64_reduced();
    let b = keys[1].as_u64_reduced();

    assert!(a < 1u64 << WIDTH);
    assert!(b < 1u64 << WIDTH);

    index_for_binary_key_for_width::<WIDTH>(a, b)
}

pub fn create_zero_entry_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = vec![[F::ZERO; 3]];
    const TABLE_NAME: &'static str = "zero entry table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        3,
        |_keys| (0, [F::ZERO; 3]),
        Some(|_| 0),
        id,
    )
}

fn index_for_binary_key(a: u64, b: u64) -> usize {
    ((a << 8) | b) as usize
}

fn index_for_binary_key_for_width<const WIDTH: usize>(a: u64, b: u64) -> usize {
    ((a << WIDTH) | b) as usize
}

pub fn create_xor_table<F: PrimeField, const WIDTH: usize>(id: u32) -> LookupTable<F, 3> {
    let keys = key_binary_generation_for_width::<F, 3, WIDTH>();
    let table_name = format!("XOR {}x{} bit table", WIDTH, WIDTH);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(
                a < 1u64 << WIDTH,
                "input 0x{:08x} is too large for {} bits",
                a,
                WIDTH
            );
            assert!(
                b < 1u64 << WIDTH,
                "input 0x{:08x} is too large for {} bits",
                b,
                WIDTH
            );

            let binop_result = a ^ b;
            let value = binop_result as u64;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(value);

            (index_for_binary_key_for_width::<WIDTH>(a, b), result)
        },
        Some(bit_chunks_index_gen_fn::<F, 3, WIDTH>),
        id,
    )
}

pub fn create_and_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_binary_generation();
    const TABLE_NAME: &'static str = "AND table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a <= u8::MAX as u64);
            assert!(b <= u8::MAX as u64);

            let binop_result = a & b;
            let value = binop_result as u64;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(value);

            (index_for_binary_key(a, b), result)
        },
        Some(u8_chunks_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_or_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_binary_generation();
    const TABLE_NAME: &'static str = "OR table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a <= u8::MAX as u64);
            assert!(b <= u8::MAX as u64);

            let binop_result = a | b;
            let value = binop_result as u64;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(value);

            (index_for_binary_key(a, b), result)
        },
        Some(u8_chunks_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_and_not_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_binary_generation();
    const TABLE_NAME: &'static str = "AND NOT table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a <= u8::MAX as u64);
            assert!(b <= u8::MAX as u64);

            let binop_result = a & (!b);
            let value = binop_result as u64;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(value);

            (index_for_binary_key(a, b), result)
        },
        Some(u8_chunks_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_quick_decoder_decomposition_table_4x4x4<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (4 + 4 + 4));
    let u4_max = 0x0f as u8;
    for a in 0..=u4_max {
        for b in 0..=u4_max {
            for c in 0..=u4_max {
                let row = [
                    F::from_u64_unchecked(a as u64),
                    F::from_u64_unchecked(b as u64),
                    F::from_u64_unchecked(c as u64),
                ];
                keys.push(row);
            }
        }
    }

    const TABLE_NAME: &'static str = "quick decoder decomposition 4x4x4 table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            let c = keys[2].as_u64_reduced();

            assert!(a < (1u64 << 4));
            assert!(b < (1u64 << 4));
            assert!(c < (1u64 << 4));

            let index = (a << 8) | (b << 4) | c;

            (index as usize, [F::ZERO; 3])
        },
        None,
        id,
    )
}

pub fn create_quick_decoder_decomposition_table_7x3x6<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (7 + 3 + 6));
    let u7_max = 0b0111_1111 as u8;
    let u3_max = 0b0111 as u8;
    let u6_max = 0b0011_1111 as u8;
    for a in 0..=u7_max {
        for b in 0..=u3_max {
            for c in 0..=u6_max {
                let row = [
                    F::from_u64_unchecked(a as u64),
                    F::from_u64_unchecked(b as u64),
                    F::from_u64_unchecked(c as u64),
                ];
                keys.push(row);
            }
        }
    }
    assert_eq!(keys.len(), 1 << (7 + 3 + 6));

    const TABLE_NAME: &'static str = "quick decoder decomposition 7x3x6 table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            let c = keys[2].as_u64_reduced();

            assert!(a < (1u64 << 7));
            assert!(b < (1u64 << 3));
            assert!(c < (1u64 << 6));

            let index = (a << 9) | (b << 6) | c;

            (index as usize, [F::ZERO; 3])
        },
        None,
        id,
    )
}

pub fn create_u16_get_sign_and_high_byte_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "U16 get sign and high byte table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16), "input value is 0x{:08x}", a);

            let sign = a >> 15;
            let high_byte = a >> 8;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(sign as u64);
            result[1] = F::from_u64_unchecked(high_byte as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_jump_cleanup_offset_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "Jump offset check-cleanup table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            let check_bit = (a >> 1) & 0x01;
            let output = a & (!0x3);

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(check_bit as u64);
            result[1] = F::from_u64_unchecked(output as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_memory_offset_lowest_bits_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "Memory offset lowest bits table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            // output lowest two bits
            let lowest = a & 0x01;
            let second = (a >> 1) & 0x01;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(lowest as u64);
            result[1] = F::from_u64_unchecked(second as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_memory_load_signs_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "Get sign bits table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            // get bits 7 and 15
            let sign_if_u8 = (a >> 7) & 0x01;
            let sign_if_u16 = (a >> 15) & 0x01;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(sign_if_u8 as u64);
            result[1] = F::from_u64_unchecked(sign_if_u16 as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_sra_sign_filler_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(1 + 1 + 5);
    const TABLE_NAME: &'static str = "SRA sign bits filler table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let input_sign = a & 1 > 0;
            let is_sra = (a >> 1) & 1 > 0;
            let shift_amount = a >> 2;
            assert!(shift_amount < 32);

            if input_sign == false || is_sra == false {
                // either it's positive, or we are not doing SRA (and it's actually the only case when shift amount can be >= 32
                // in practice, but we have to fill the table)
                let result = [F::ZERO; 3];

                (a as usize, result)
            } else {
                if shift_amount == 0 {
                    // special case
                    let result = [F::ZERO; 3];

                    (a as usize, result)
                } else {
                    let (mask, _) = u32::MAX.overflowing_shl(32 - (shift_amount as u32));

                    let mut result = [F::ZERO; 3];
                    result[0] = F::from_u64_unchecked(mask as u16 as u64);
                    result[1] = F::from_u64_unchecked((mask >> 16) as u16 as u64);

                    (a as usize, result)
                }
            }
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_conditional_op_resolution_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    const TABLE_WIDTH: usize = 3 + 1 + 1 + 1 + 1;
    const FUNCT3_MASK: u64 = 0x7u64;
    const UNSIGNED_LT_BIT_SHIFT: usize = 3;
    const EQ_BIT_SHIFT: usize = 4;
    const SRC1_BIT_SHIFT: usize = 5;
    const SRC2_BIT_SHIFT: usize = 6;

    let keys = key_for_continuous_log2_range(TABLE_WIDTH);
    const TABLE_NAME: &'static str = "Conditional family resolution table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << TABLE_WIDTH));

            let input = a;
            let funct3 = input & FUNCT3_MASK;
            let unsigned_lt_flag = (input & (1 << UNSIGNED_LT_BIT_SHIFT)) != 0;
            let eq_flag = (input & (1 << EQ_BIT_SHIFT)) != 0;
            let src1_bit = (input & (1 << SRC1_BIT_SHIFT)) != 0;
            let src2_bit = (input & (1 << SRC2_BIT_SHIFT)) != 0;
            let operands_different_signs_flag = src1_bit ^ src2_bit;

            let (should_branch, should_store) = match funct3 {
                0b000 => {
                    // BEQ
                    if eq_flag {
                        (true, false)
                    } else {
                        (false, false)
                    }
                }
                0b001 => {
                    // BNE
                    if eq_flag == false {
                        (true, false)
                    } else {
                        (false, false)
                    }
                }
                0b010 => {
                    // STL
                    if operands_different_signs_flag {
                        // signs are different,
                        // so if rs1 is negative, and rs2 is positive (so condition holds)
                        // then LT must be be false
                        if unsigned_lt_flag == false {
                            (false, true)
                        } else {
                            (false, false)
                        }
                    } else {
                        // just unsigned comparison works for both cases
                        if unsigned_lt_flag {
                            (false, true)
                        } else {
                            (false, false)
                        }
                    }
                }
                0b011 => {
                    // STLU
                    // just unsigned comparison works for both cases
                    if unsigned_lt_flag {
                        (false, true)
                    } else {
                        (false, false)
                    }
                }
                0b100 => {
                    // BLT
                    if operands_different_signs_flag {
                        // signs are different,
                        // so if rs1 is negative, and rs2 is positive (so condition holds)
                        // then LT must be be false
                        if unsigned_lt_flag == false {
                            (true, false)
                        } else {
                            (false, false)
                        }
                    } else {
                        // just unsigned comparison works for both cases
                        if unsigned_lt_flag {
                            (true, false)
                        } else {
                            (false, false)
                        }
                    }
                }
                0b101 => {
                    // BGE
                    // inverse of BLT
                    if operands_different_signs_flag {
                        if unsigned_lt_flag == false {
                            (false, false)
                        } else {
                            (true, false)
                        }
                    } else {
                        if unsigned_lt_flag {
                            (false, false)
                        } else {
                            (true, false)
                        }
                    }
                }
                0b110 => {
                    // BLTU
                    if unsigned_lt_flag {
                        (true, false)
                    } else {
                        (false, false)
                    }
                }
                0b111 => {
                    // BGEU
                    // inverse of BLTU
                    if unsigned_lt_flag {
                        (false, false)
                    } else {
                        (true, false)
                    }
                }

                _ => {
                    unreachable!()
                }
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(should_branch as u64);
            result[1] = F::from_u64_unchecked(should_store as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_rom_separator_table<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    id: u32,
) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "ROM address space separator table";
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            let bound = 1 << ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
            let input = a;
            let is_ram = input >= bound;
            let rom_chunk = input % bound;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(is_ram as u64);
            result[1] = F::from_u64_unchecked(rom_chunk);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

// we make it so that index in the table is just (key0 << 8) || key1
pub fn key_binary_generation<F: PrimeField, const N: usize>() -> Vec<[F; N]> {
    let mut keys = Vec::with_capacity(1 << 16);
    for a in 0..(1u64 << 8) {
        for b in 0..(1u64 << 8) {
            let mut key = [F::ZERO; N];
            key[0] = F::from_u64_unchecked(a as u64);
            key[1] = F::from_u64_unchecked(b as u64);
            keys.push(key);
        }
    }

    keys
}

// we make it so that index in the table is just (key0 << WIDTH) || key1
pub fn key_binary_generation_for_width<F: PrimeField, const N: usize, const WIDTH: usize>(
) -> Vec<[F; N]> {
    let mut keys = Vec::with_capacity(1 << (WIDTH * 2));
    for a in 0..(1u64 << WIDTH) {
        for b in 0..(1u64 << WIDTH) {
            let mut key = [F::ZERO; N];
            key[0] = F::from_u64_unchecked(a as u64);
            key[1] = F::from_u64_unchecked(b as u64);
            keys.push(key);
        }
    }

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
    let keys: Vec<_> = (0..=max_value_inclusive)
        .map(|a| {
            let mut key = [F::ZERO; N];
            key[0] = F::from_u64_with_reduction(a);

            key
        })
        .collect();

    assert_eq!(keys.len(), max_value_inclusive as usize + 1);

    keys
}

pub fn key_get_bit<F: PrimeField, const N: usize>() -> Vec<SmallVec<[F; N]>> {
    let keys = (0..=u16::MAX)
        .flat_map(|a| {
            (0..16).map(move |b| {
                smallvec::smallvec![
                    F::from_u64_unchecked(a as u64),
                    F::from_u64_unchecked(b as u64)
                ]
            })
        })
        .collect();

    keys
}

pub fn create_range_check_table<F: PrimeField, const M: usize>(id: u32) -> LookupTable<F, 1> {
    assert!(M > 0);
    let keys = key_for_continuous_log2_range(M);
    let table_name = format!("Range check {} bits table", M);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << M));

            (a as usize, [F::ZERO])
        },
        Some(first_key_index_gen_fn::<F, 1>),
        id,
    )
}

pub fn create_formal_width_3_range_check_table_for_two_tuple<F: PrimeField, const M: usize>(
    id: u32,
) -> LookupTable<F, 3> {
    assert!(M > 0);
    let mut keys = Vec::with_capacity(1 << (M * 2));
    for first in 0..(1 << M) {
        for second in 0..(1 << M) {
            let key = [
                F::from_u64_unchecked(first as u64),
                F::from_u64_unchecked(second as u64),
                F::ZERO,
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Range check {} bits table", M);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            assert!(keys[2].is_zero());
            assert!(a < (1u64 << M));
            assert!(b < (1u64 << M));

            (((a << M) | b) as usize, [F::ZERO; 3])
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            assert!(keys[2].is_zero());
            assert!(a < (1u64 << M));
            assert!(b < (1u64 << M));

            ((a << M) | b) as usize
        }),
        id,
    )
}

pub fn create_formal_width_3_range_check_table_for_single_entry<F: PrimeField, const M: usize>(
    id: u32,
) -> LookupTable<F, 3> {
    assert!(M > 0);
    let mut keys = Vec::with_capacity(1 << M);
    for first in 0..(1 << M) {
        let key = [F::from_u64_unchecked(first as u64), F::ZERO, F::ZERO];
        keys.push(key)
    }
    let table_name = format!("Width-3 range check {} bits table", M);
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(keys[1].is_zero());
            assert!(keys[2].is_zero());
            assert!(a < (1u64 << M));

            (a as usize, [F::ZERO; 3])
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            assert!(keys[1].is_zero());
            assert!(keys[2].is_zero());
            assert!(a < (1u64 << M));

            a as usize
        }),
        id,
    )
}

pub fn create_shift_implementation_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    // take 16 bits of input half-word || shift || is_right

    let keys = key_for_continuous_log2_range(16 + 5 + 1);

    let table_name = "Shift implementation table".to_string();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let input_word = a as u16;
            let shift_amount = ((a >> 16) & 0b1_1111) as u32;
            let is_right_shift = (a >> (16 + 5)) > 0;

            let (in_place, overflow) = if is_right_shift {
                let input = (input_word as u32) << 16;
                let t = input >> shift_amount;
                let in_place = (t >> 16) as u16;
                let overflow = t as u16;

                (in_place, overflow)
            } else {
                let input = input_word as u32;
                let t = input << shift_amount;
                let in_place = t as u16;
                let overflow = (t >> 16) as u16;

                (in_place, overflow)
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(in_place as u64);
            result[1] = F::from_u64_unchecked(overflow as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_select_byte_and_get_sign_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    // This table takes a word + single bit, and selected a byte + gets sign on the byte
    let keys = key_for_continuous_log2_range(16 + 1);

    let table_name = "Select byte and get sign table".to_string();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < 1 << 17);

            let word = a as u16;
            let selector_bit = (a >> 16) != 0;

            let selected_byte = if selector_bit {
                (word >> 8) as u8
            } else {
                word as u8
            };

            let sign_bit = selected_byte & (1 << 7) != 0;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(selected_byte as u64);
            result[1] = F::from_boolean(sign_bit);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_truncate_shift_amount_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (8 + 1));
    for first in 0..(1 << 8) {
        for second in 0..(1 << 1) {
            let key = [
                F::from_u64_unchecked(first as u64),
                F::from_u64_unchecked(second as u64),
                F::ZERO,
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Truncate and adjust shift amount");
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        3,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();
            assert!(a < 1 << 8);

            let is_right_shift = b != 0;
            let shift_amount = a & 0b1_1111;
            let shift_amount = if is_right_shift {
                shift_amount
            } else {
                32 - shift_amount
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(shift_amount as u64);

            (((a << 1) | b) as usize, result)
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a < (1u64 << 8));
            assert!(b < (1u64 << 1));

            ((a << 1) | b) as usize
        }),
        id,
    )
}

pub fn create_mem_load_extend_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    // 16-bit half-word || low/high value bit || funct3
    let keys = key_for_continuous_log2_range(16 + 1 + 3);

    let table_name = "Extend LOAD value table".to_string();
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < 1 << (16 + 1 + 3));

            let word = a as u16;
            let use_high_half = ((a >> 16) & 1) != 0;
            let funct3 = (a >> 17) as u8;

            let selected_byte = if use_high_half {
                (word >> 8) as u8
            } else {
                word as u8
            };

            #[allow(non_snake_case)]
            let loaded_word = match funct3 {
                _LB @ 0b000 => {
                    // sign-extend selected byte
                    let sign = (selected_byte >> 7) != 0;
                    if sign {
                        (selected_byte as u32) | 0xffffff00
                    } else {
                        selected_byte as u32
                    }
                }
                _LBU @ 0b100 => {
                    // zero-extend selected byte
                    selected_byte as u32
                }
                _LH @ 0b001 => {
                    // sign-extend selected word
                    let sign = (word >> 15) != 0;
                    if sign {
                        (word as u32) | 0xffff0000
                    } else {
                        word as u32
                    }
                }
                _LHU @ 0b101 => {
                    // zero-extend selected word
                    word as u32
                }
                _ => {
                    // Not important
                    0u32
                }
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked((loaded_word & 0xffff) as u64);
            result[1] = F::from_u64_unchecked((loaded_word >> 16) as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub fn create_store_byte_source_contribution_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (16 + 1));
    for first in 0..(1 << 16) {
        for second in 0..(1 << 1) {
            let key = [
                F::from_u64_unchecked(first as u64),
                F::from_u64_unchecked(second as u64),
                F::ZERO,
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Store byte source contribution table");
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            let bit_0 = b != 0;
            let byte = a as u8;
            let result_half_word = if bit_0 {
                (byte as u16) << 8
            } else {
                byte as u16
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(result_half_word as u64);

            (((a << 1) | b) as usize, result)
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a < (1u64 << 16));
            assert!(b < (1u64 << 1));

            ((a << 1) | b) as usize
        }),
        id,
    )
}

pub fn create_store_byte_existing_contribution_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let mut keys = Vec::with_capacity(1 << (16 + 1));
    for first in 0..(1 << 16) {
        for second in 0..(1 << 1) {
            let key = [
                F::from_u64_unchecked(first as u64),
                F::from_u64_unchecked(second as u64),
                F::ZERO,
            ];
            keys.push(key)
        }
    }
    let table_name = format!("Store byte existing contribution table");
    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        2,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            // we need to cleanup a part of it to prepare for addition
            let bit_0 = b != 0;
            let result_half_word = if bit_0 {
                (a as u16) & 0x00ff
            } else {
                (a as u16) & 0xff00
            };

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(result_half_word as u64);

            (((a << 1) | b) as usize, result)
        },
        Some(|keys| {
            let a = keys[0].as_u64_reduced();
            let b = keys[1].as_u64_reduced();

            assert!(a < (1u64 << 16));
            assert!(b < (1u64 << 1));

            ((a << 1) | b) as usize
        }),
        id,
    )
}

pub fn create_pow2_table<F: PrimeField, const WIDTH: usize>(id: u32) -> LookupTable<F, 3> {
    // also support formal 1<<width as place 0 in such cases
    let keys = key_for_continuous_range(1u64 << WIDTH);
    const MASK: u64 = (1u64 << 16) - 1;
    let table_name = format!("Powers of 2 table up to {} value", (1 << WIDTH) - 1);

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        table_name,
        1,
        |keys| {
            let max_value: u64 = 1u64 << WIDTH;
            let a = keys[0].as_u64_reduced();
            assert!(a <= max_value);
            if a == max_value {
                let result = [F::ZERO; 3];

                (a as usize, result)
            } else {
                let mut result = [F::ZERO; 3];
                let pow_of_2 = 1u64 << a;
                let low: u64 = pow_of_2 & MASK;
                let high = pow_of_2 >> 16;

                result[0] = F::from_u64_unchecked(low as u64);
                result[1] = F::from_u64_unchecked(high as u64);

                (a as usize, result)
            }
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

// We have 11 available opcodes [LOAD, MISC_MEM, OP_IMM, AUIPC, STORE, OP, LUI, BRANCH, JALR, JAL, SYSTEM].
// Not all binary combinations 2^7 exist an opcode so we add an extra flag for this OP_INVALID,
// as a result we get bitmask with 12 bits
pub fn create_op_bitmask_table<F: PrimeField>(_id: u32) -> LookupTable<F, 3> {
    unimplemented!("no longer used");
}

pub fn create_u16_split_into_bytes_table<F: PrimeField>(id: u32) -> LookupTable<F, 3> {
    let keys = key_for_continuous_log2_range(16);
    const TABLE_NAME: &'static str = "U16 split into bytes table";

    LookupTable::create_table_from_key_and_pure_generation_fn(
        &keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            assert!(a < (1u64 << 16));

            let low_byte = a & 0xff;
            let high_byte = a >> 8;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(low_byte as u64);
            result[1] = F::from_u64_unchecked(high_byte as u64);

            (a as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}

pub const TABLE_TYPES_UPPER_BOUNDS: usize = const {
    if TOTAL_NUM_OF_TABLES < 48 {
        TOTAL_NUM_OF_TABLES
    } else {
        48
    }
};

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

    pub fn materialize_table(&mut self, table_type: TableType) {
        let table = table_type.generate_table::<F>();
        self.add_table_with_content(table_type, table);
    }

    #[track_caller]
    #[inline(always)]
    pub fn lookup_values<const N: usize>(&self, keys: &[F], id: u32) -> [F; N] {
        let table = &self.tables[id as usize];
        debug_assert!(
            table.is_initialized(),
            "table with id = {:?} is not initialized",
            id
        );
        let values = table.lookup_value::<N>(keys);

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
        debug_assert!(
            table.is_initialized(),
            "table with id = {:?} is not initialized",
            id
        );
        let (mut index, values) = table.lookup_values_and_get_index::<N>(keys);
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
        debug_assert!(
            table.is_initialized(),
            "table with id = {:?} is not initialized",
            id
        );
        let mut index = table.lookup_row(keys);
        index += offset;

        index
    }

    // #[inline(always)]
    // pub fn lookup_row(&self, row: &[F], id: u32) -> bool {
    //     self.tables[id as usize].lookup_row(row).is_some()
    // }

    #[inline(always)]
    pub fn get_start_table_offset(&self, id: u32) -> usize {
        self.offsets_for_multiplicities[id as usize]
    }

    pub fn table_starts_offsets(&self) -> [usize; TABLE_TYPES_UPPER_BOUNDS] {
        self.offsets_for_multiplicities
    }

    #[inline(always)]
    pub fn get_table(&self, table_type: TableType) -> &LookupWrapper<F> {
        &self.tables[table_type.to_table_id() as usize]
    }

    #[inline(always)]
    pub fn get_table_by_id(&self, id: u32) -> &LookupWrapper<F> {
        &self.tables[id as usize]
    }

    pub fn dump_tables(&self) -> Vec<[F; 4]> {
        let mut result = Vec::with_capacity(self.total_tables_len);
        for table in self.tables.iter() {
            if table.get_size() == 0 {
                continue;
            }
            let id = table.get_table_id();
            table.dump_into(&mut result, Some(id));
        }

        result
    }
}

#[cfg(test)]
mod test {
    use field::Mersenne31Field;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::BTreeMap;
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn bench_btree_lookup() {
        let table = TableType::Xor.generate_table::<Mersenne31Field>();
        let num_queries = 1 << 23;
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let queries: Vec<[Mersenne31Field; 2]> = (0..num_queries)
            .map(|_| {
                let a: u8 = rng.random();
                let b: u8 = rng.random();

                [Mersenne31Field(a as u32), Mersenne31Field(b as u32)]
            })
            .collect();

        let current_time = std::time::Instant::now();
        for input in queries.iter() {
            let _ = table.lookup_value::<1>(input);
        }
        dbg!(current_time.elapsed());

        // simulate as hashmap
        let mut map = HashMap::new();
        let LookupWrapper::Dimensional3(table) = &table else {
            unreachable!()
        };

        for (k, v) in table.lookup_data.iter() {
            map.insert(k.clone(), v.clone());
        }

        let hashmap_time = std::time::Instant::now();
        for input in queries.iter() {
            let key = LookupKey::<Mersenne31Field, 3>::from_keys(input);
            let _ = map.get(&key);
        }
        dbg!(hashmap_time.elapsed());

        // simulate as btree without indirection
        let mut btree = BTreeMap::new();

        for (k, v) in table.lookup_data.iter() {
            btree.insert(k.clone(), v.clone());
        }

        let btree_time = std::time::Instant::now();
        for input in queries.iter() {
            let key = LookupKey::<Mersenne31Field, 3>::from_keys(input);
            let _ = btree.get(&key);
        }
        dbg!(btree_time.elapsed());

        // simulate as ordered vector
        let mut ordered_vector = Vec::new();

        for (k, v) in table.lookup_data.iter() {
            ordered_vector.push((k.clone(), v.clone()));
        }

        ordered_vector.sort_by(|a, b| a.0.cmp(&b.0));

        let vec_time = std::time::Instant::now();
        for input in queries.iter() {
            let key = LookupKey::<Mersenne31Field, 3>::from_keys(input);
            let _ = ordered_vector.binary_search_by_key(&key, |(a, _)| a.clone());
        }
        dbg!(vec_time.elapsed());
    }
}
