use std::alloc::Allocator;

use crate::jit::{CounterType, MAX_NUM_COUNTERS, MAX_TRACE_CHUNK_LEN};

use super::*;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DelegationsCounters {
    pub non_determinism_reads: usize,
    pub blake_calls: usize,
    pub bigint_calls: usize,
    pub keccak_calls: usize,
}

impl Counters for DelegationsCounters {
    #[inline(always)]
    fn bump_bigint(&mut self, by: usize) {
        self.bigint_calls += by;
    }
    #[inline(always)]
    fn bump_blake2_round_function(&mut self, by: usize) {
        self.blake_calls += by;
    }
    #[inline(always)]
    fn bump_keccak_special5(&mut self, by: usize) {
        self.keccak_calls += by;
    }
    #[inline(always)]
    fn log_circuit_family<const FAMILY: u8>(&mut self) {}
    #[inline(always)]
    fn log_multiple_circuit_family_calls<const FAMILY: u8>(&mut self, _num_calls: usize) {}
    #[inline(always)]
    fn get_calls_to_circuit_family<const FAMILY: u8>(&self) -> usize {
        0
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DelegationsAndFamiliesCounters {
    pub add_sub_family: usize,
    pub binary_shift_csr_family: usize,
    pub slt_branch_family: usize,
    pub mul_div_family: usize,
    pub word_size_mem_family: usize,
    pub subword_size_mem_family: usize,
    pub blake_calls: usize,
    pub bigint_calls: usize,
    pub keccak_calls: usize,
}

impl Counters for DelegationsAndFamiliesCounters {
    #[inline(always)]
    fn bump_bigint(&mut self, by: usize) {
        self.bigint_calls += by;
    }
    #[inline(always)]
    fn bump_blake2_round_function(&mut self, by: usize) {
        self.blake_calls += by;
    }
    #[inline(always)]
    fn bump_keccak_special5(&mut self, by: usize) {
        self.keccak_calls += by;
    }
    #[inline(always)]
    fn log_circuit_family<const FAMILY: u8>(&mut self) {
        if const { FAMILY == ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX } {
            self.add_sub_family += 1;
        } else if const { FAMILY == JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX } {
            self.slt_branch_family += 1;
        } else if const { FAMILY == SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX } {
            self.binary_shift_csr_family += 1;
        } else if const { FAMILY == MUL_DIV_CIRCUIT_FAMILY_IDX } {
            self.mul_div_family += 1;
        } else if const { FAMILY == LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.word_size_mem_family += 1;
        } else if const { FAMILY == LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.subword_size_mem_family += 1;
        } else {
            unsafe { core::hint::unreachable_unchecked() }
        }
    }
    #[inline(always)]
    fn log_multiple_circuit_family_calls<const FAMILY: u8>(&mut self, num_calls: usize) {
        if const { FAMILY == ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX } {
            self.add_sub_family += num_calls;
        } else if const { FAMILY == JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX } {
            self.slt_branch_family += num_calls;
        } else if const { FAMILY == SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX } {
            self.binary_shift_csr_family += num_calls;
        } else if const { FAMILY == MUL_DIV_CIRCUIT_FAMILY_IDX } {
            self.mul_div_family += num_calls;
        } else if const { FAMILY == LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.word_size_mem_family += num_calls;
        } else if const { FAMILY == LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.subword_size_mem_family += num_calls;
        } else {
            unsafe { core::hint::unreachable_unchecked() }
        }
    }
    #[inline(always)]
    fn get_calls_to_circuit_family<const FAMILY: u8>(&self) -> usize {
        if const { FAMILY == ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX } {
            self.add_sub_family
        } else if const { FAMILY == JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX } {
            self.slt_branch_family
        } else if const { FAMILY == SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX } {
            self.binary_shift_csr_family
        } else if const { FAMILY == MUL_DIV_CIRCUIT_FAMILY_IDX } {
            self.mul_div_family
        } else if const { FAMILY == LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.word_size_mem_family
        } else if const { FAMILY == LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.subword_size_mem_family
        } else {
            unsafe { core::hint::unreachable_unchecked() }
        }
    }
}

impl From<[u32; MAX_NUM_COUNTERS]> for DelegationsAndFamiliesCounters {
    fn from(counters: [u32; MAX_NUM_COUNTERS]) -> Self {
        Self {
            add_sub_family: counters[CounterType::AddSubLui as u8 as usize] as usize,
            slt_branch_family: counters[CounterType::BranchSlt as u8 as usize] as usize,
            binary_shift_csr_family: counters[CounterType::ShiftBinaryCsr as u8 as usize] as usize,
            mul_div_family: counters[CounterType::MulDiv as u8 as usize] as usize,
            word_size_mem_family: counters[CounterType::MemWord as u8 as usize] as usize,
            subword_size_mem_family: counters[CounterType::MemSubword as u8 as usize] as usize,
            blake_calls: counters[CounterType::BlakeDelegation as u8 as usize] as usize,
            bigint_calls: counters[CounterType::BigintDelegation as u8 as usize] as usize,
            keccak_calls: counters[CounterType::KeccakDelegation as u8 as usize] as usize,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DelegationsAndUnifiedCounters {
    pub non_determinism_reads: usize,
    pub blake_calls: usize,
    pub bigint_calls: usize,
    pub keccak_calls: usize,
    pub cycles: usize,
}

impl Counters for DelegationsAndUnifiedCounters {
    #[inline(always)]
    fn bump_bigint(&mut self, by: usize) {
        self.bigint_calls += by;
    }
    #[inline(always)]
    fn bump_blake2_round_function(&mut self, by: usize) {
        self.blake_calls += by;
    }
    #[inline(always)]
    fn bump_keccak_special5(&mut self, by: usize) {
        self.keccak_calls += by;
    }
    #[inline(always)]
    fn log_circuit_family<const FAMILY: u8>(&mut self) {
        if const { FAMILY == ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX } {
            self.cycles += 1;
        } else if const { FAMILY == JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX } {
            self.cycles += 1;
        } else if const { FAMILY == SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX } {
            self.cycles += 1;
        } else if const { FAMILY == MUL_DIV_CIRCUIT_FAMILY_IDX } {
            self.cycles += 1;
        } else if const { FAMILY == LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.cycles += 1;
        } else if const { FAMILY == LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.cycles += 1;
        } else {
            unsafe { core::hint::unreachable_unchecked() }
        }
    }
    #[inline(always)]
    fn log_multiple_circuit_family_calls<const FAMILY: u8>(&mut self, num_calls: usize) {
        if const { FAMILY == ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX } {
            self.cycles += num_calls;
        } else if const { FAMILY == JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX } {
            self.cycles += num_calls;
        } else if const { FAMILY == SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX } {
            self.cycles += num_calls;
        } else if const { FAMILY == MUL_DIV_CIRCUIT_FAMILY_IDX } {
            self.cycles += num_calls;
        } else if const { FAMILY == LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.cycles += num_calls;
        } else if const { FAMILY == LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX } {
            self.cycles += num_calls;
        } else {
            unsafe { core::hint::unreachable_unchecked() }
        }
    }
    #[inline(always)]
    fn get_calls_to_circuit_family<const FAMILY: u8>(&self) -> usize {
        if const { FAMILY == REDUCED_MACHINE_CIRCUIT_FAMILY_IDX } {
            self.cycles
        } else {
            panic!("Must be called with reduced machine family only");
        }
    }
}

impl From<[u32; MAX_NUM_COUNTERS]> for DelegationsAndUnifiedCounters {
    fn from(counters: [u32; MAX_NUM_COUNTERS]) -> Self {
        let add_sub_family = counters[CounterType::AddSubLui as u8 as usize] as usize;
        let slt_branch_family = counters[CounterType::BranchSlt as u8 as usize] as usize;
        let binary_shift_csr_family = counters[CounterType::ShiftBinaryCsr as u8 as usize] as usize;
        let mul_div_family = counters[CounterType::MulDiv as u8 as usize] as usize;
        let word_size_mem_family = counters[CounterType::MemWord as u8 as usize] as usize;
        let subword_size_mem_family = counters[CounterType::MemSubword as u8 as usize] as usize;
        let cycles = add_sub_family
            + slt_branch_family
            + binary_shift_csr_family
            + mul_div_family
            + word_size_mem_family
            + subword_size_mem_family;
        Self {
            non_determinism_reads: 0,
            blake_calls: counters[CounterType::BlakeDelegation as u8 as usize] as usize,
            bigint_calls: counters[CounterType::BigintDelegation as u8 as usize] as usize,
            keccak_calls: counters[CounterType::KeccakDelegation as u8 as usize] as usize,
            cycles,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SimpleSnapshot<C: Counters> {
    pub state: State<C>,
    pub reads_start: usize,
    pub reads_end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PartialSnapshot {
    pub reads_offset: usize,
}

pub trait ReplayBuffer<T: Sized> {
    fn new_with_snapshots_bound(bound: usize) -> Self;
    unsafe fn push_within_capacity_unchecked(&mut self, value: T);
    fn make_range<'a>(&'a self, range: core::ops::Range<usize>) -> Vec<&'a [T]>
    where
        T: 'a;
    fn len(&self) -> usize;
}

impl<T: Sized, A: Allocator + Default> ReplayBuffer<T> for Vec<T, A> {
    fn new_with_snapshots_bound(bound: usize) -> Self {
        Vec::<T, A>::with_capacity_in(bound, A::default())
    }
    #[inline(always)]
    unsafe fn push_within_capacity_unchecked(&mut self, value: T) {
        self.push_within_capacity(value).unwrap_unchecked();
    }
    #[inline(always)]
    fn len(&self) -> usize {
        Vec::<T, A>::len(self)
    }
    fn make_range<'a>(&'a self, range: core::ops::Range<usize>) -> Vec<&'a [T]>
    where
        T: 'a,
    {
        vec![&self[range]]
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecBiVec<T: Sized, const I: usize = { 1 << 30 }, const O: usize = 4> {
    current: usize,
    total_len: usize,
    buffers: [Vec<T>; O],
}

impl<T: Sized, const I: usize, const O: usize> SpecBiVec<T, I, O> {
    fn new() -> Self {
        assert!(O > 0);
        assert!(I > 0);
        assert!(O * I <= 1 << 36);
        let mut buffers: [Vec<T>; O] = std::array::from_fn(|_| Vec::new());
        buffers[0] = Vec::with_capacity(I);

        Self {
            current: 0,
            total_len: 0,
            buffers,
        }
    }

    #[inline(always)]
    fn push_unchecked_impl(&mut self, value: T) {
        unsafe {
            let dst = self.buffers.get_unchecked_mut(self.current);
            if core::hint::unlikely(dst.len() == I) {
                let mut next = Vec::with_capacity(I);
                next.push_within_capacity(value).unwrap_unchecked();
                self.current += 1;
                self.buffers[self.current] = next;
            } else {
                dst.push_within_capacity(value).unwrap_unchecked();
            }
            self.total_len += 1;
        }
    }

    pub fn make_range_impl<'a>(&'a self, range: core::ops::Range<usize>) -> Vec<&'a [T]>
    where
        T: 'a,
    {
        assert!(range.end <= self.total_len);
        let (s_o, s_i) = (range.start / I, range.start % I);
        let (e_o, e_i) = (range.end / I, range.end % I);

        let mut result = Vec::with_capacity(e_o + 1 - s_o);
        let mut inner_offset = s_i;
        for i in s_o..=e_o {
            if i == e_o {
                if e_i != 0 {
                    result.push(&self.buffers[i][inner_offset..e_i]);
                }
            } else {
                result.push(&self.buffers[i][inner_offset..]);
                inner_offset = 0;
            }
        }

        result
    }
}

impl<T: Sized, const I: usize, const O: usize> ReplayBuffer<T> for SpecBiVec<T, I, O> {
    fn new_with_snapshots_bound(bound: usize) -> Self {
        assert!(bound <= I * O);
        Self::new()
    }
    #[inline(always)]
    unsafe fn push_within_capacity_unchecked(&mut self, value: T) {
        Self::push_unchecked_impl(self, value);
    }
    #[inline(always)]
    fn len(&self) -> usize {
        self.total_len
    }
    fn make_range<'a>(&'a self, range: core::ops::Range<usize>) -> Vec<&'a [T]>
    where
        T: 'a,
    {
        Self::make_range_impl(self, range)
    }
}

pub struct SimpleSnapshotter<
    C: Counters,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
    MB: ReplayBuffer<(u32, (u32, u32))> = Vec<(u32, (u32, u32))>,
> {
    pub current_partial_snapshot: PartialSnapshot,
    pub snapshots: Vec<SimpleSnapshot<C>>,
    pub reads_buffer: MB,
    pub initial_snapshot: SimpleSnapshot<C>,
}

impl<C: Counters, const ROM_BOUND_SECOND_WORD_BITS: usize, MB: ReplayBuffer<(u32, (u32, u32))>>
    SimpleSnapshotter<C, ROM_BOUND_SECOND_WORD_BITS, MB>
{
    pub fn new_with_cycle_limit(limit: usize, initial_state: State<C>) -> Self {
        let initial_snapshot = SimpleSnapshot {
            state: initial_state,
            reads_start: 0,
            reads_end: 0,
        };

        let worst_period = MAX_TRACE_CHUNK_LEN;
        let worst_case_num_snapshots = limit.div_ceil(worst_period);

        Self {
            current_partial_snapshot: PartialSnapshot { reads_offset: 0 },
            snapshots: Vec::with_capacity(worst_case_num_snapshots),
            reads_buffer: MB::new_with_snapshots_bound(limit),
            initial_snapshot,
        }
    }

    fn snapshot_impl(&mut self, state: &State<C>) {
        let new_snapshot = SimpleSnapshot {
            state: *state,
            reads_start: self.current_partial_snapshot.reads_offset,
            reads_end: self.reads_buffer.len(),
        };
        self.current_partial_snapshot.reads_offset = self.reads_buffer.len();
        self.snapshots.push(new_snapshot);
    }
}

impl<C: Counters, const ROM_BOUND_SECOND_WORD_BITS: usize, MB: ReplayBuffer<(u32, (u32, u32))>>
    Snapshotter<C> for SimpleSnapshotter<C, ROM_BOUND_SECOND_WORD_BITS, MB>
{
    #[inline(always)]
    fn take_snapshot_if_needed(&mut self, state: &State<C>) -> bool {
        use crate::jit::{MAX_TRACE_CHUNK_LEN, TRACE_CHUNK_LEN};
        if self.reads_buffer.len() - self.current_partial_snapshot.reads_offset >= TRACE_CHUNK_LEN {
            debug_assert!(
                self.reads_buffer.len() - self.current_partial_snapshot.reads_offset
                    <= MAX_TRACE_CHUNK_LEN
            );
            self.snapshot_impl(state);
        }
        false
    }

    #[inline(always)]
    fn take_final_snapshot(&mut self, state: &State<C>) {
        self.snapshot_impl(state);
    }

    #[inline(always)]
    fn append_arbitrary_value(&mut self, value: u32) {
        unsafe {
            self.reads_buffer
                .push_within_capacity_unchecked((value, (0u32, 0u32)));
        }
    }

    #[inline(always)]
    fn append_memory_read(
        &mut self,
        address: u32,
        read_value: u32,
        read_timestamp: TimestampScalar,
        _write_timestamp: TimestampScalar,
    ) {
        unsafe {
            self.reads_buffer.push_within_capacity_unchecked((
                read_value,
                (read_timestamp as u32, (read_timestamp >> 32) as u32),
            ));
        }
    }
}
