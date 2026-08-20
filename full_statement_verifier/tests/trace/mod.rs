use std::cell::Cell;
use std::rc::Rc;

use common_constants::{TimestampScalar, INITIAL_TIMESTAMP, ROM_SECOND_WORD_BITS, TIMESTAMP_STEP};
use full_statement_verifier::host_utils::cost_model::census::{CensusVec, NUM_CENSUS_DIMS, NUM_FAMILY_DIMS};
use full_statement_verifier::program_proof::ProgramProof;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::vm::{
    Counters, DelegationsAndUnifiedCounters, NonDeterminismCSRSource, RamPeek, RamWithRomRegion,
    SimpleSnapshotter, SimpleTape, Snapshotter, State, VM,
};
use setups::Setups;
use verifier_common::field::baby_bear::base::BabyBearField;

pub mod calibrate;
pub mod plan;

const UNROLLED_RECURSION_CYCLES_BOUND: usize = 1 << 28;
const RAM_BOUND: usize = 1 << 30;

/// Per-family cycle and delegation-call counters in `CENSUS_DIMS` order.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CensusCounters {
    pub dims: [usize; NUM_CENSUS_DIMS],
}

const fn family_slot(family: u8) -> usize {
    match family {
        common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX => 0,
        common_constants::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX => 1,
        common_constants::SHIFT_BINARY_CIRCUIT_FAMILY_IDX => 2,
        common_constants::MUL_DIV_CIRCUIT_FAMILY_IDX => 3,
        common_constants::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX => 4,
        common_constants::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX => 5,
        _ => panic!("unexpected circuit family on the unrolled verifier machine"),
    }
}

impl Counters for CensusCounters {
    fn bump_bigint(&mut self, by: usize) {
        self.dims[NUM_FAMILY_DIMS + 1] += by;
    }
    fn bump_blake2_round_function(&mut self, by: usize) {
        self.dims[NUM_FAMILY_DIMS] += by;
    }
    fn bump_keccak_special5(&mut self, by: usize) {
        self.dims[NUM_FAMILY_DIMS + 2] += by;
    }
    fn bump_blake2_g_function(&mut self, by: usize) {
        self.dims[NUM_FAMILY_DIMS + 3] += by;
    }
    fn log_multiple_circuit_family_calls<const FAMILY: u8>(&mut self, num_calls: usize) {
        self.dims[const { family_slot(FAMILY) }] += num_calls;
    }
    fn get_calls_to_circuit_family<const FAMILY: u8>(&self) -> usize {
        self.dims[const { family_slot(FAMILY) }]
    }
}

fn census_of(c: &CensusCounters) -> CensusVec {
    c.dims.map(|v| v as u64)
}

struct MarkingSnapshotter {
    cell: Rc<Cell<(TimestampScalar, CensusCounters)>>,
}

impl Snapshotter<CensusCounters> for MarkingSnapshotter {
    fn take_snapshot_if_needed(&mut self, state: &State<CensusCounters>) -> bool {
        self.cell.set((state.timestamp, state.counters));
        false
    }
    fn take_final_snapshot(&mut self, state: &State<CensusCounters>) {
        self.cell.set((state.timestamp, state.counters));
    }
    fn append_arbitrary_value(&mut self, _value: u32) {}
    fn append_memory_read(
        &mut self,
        _address: u32,
        _read_value: u32,
        _read_timestamp: TimestampScalar,
        _write_timestamp: TimestampScalar,
    ) {
    }
}

struct StampingSource<S> {
    inner: S,
    cell: Rc<Cell<(TimestampScalar, CensusCounters)>>,
    marks: Vec<TimestampScalar>,
    census_marks: Vec<CensusVec>,
}

impl<S: NonDeterminismCSRSource> NonDeterminismCSRSource for StampingSource<S> {
    fn read(&mut self) -> u32 {
        let (timestamp, counters) = self.cell.get();
        self.marks.push(timestamp);
        self.census_marks.push(census_of(&counters));
        self.inner.read()
    }
    fn write_with_memory_access<R: RamPeek>(&mut self, ram: &R, value: u32) {
        self.inner.write_with_memory_access(ram, value);
    }
    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32) {
        self.inner.write_with_memory_access_dyn(ram, value);
    }
}

pub struct Trace {
    pub marks: Vec<u64>,
    pub census_marks: Vec<CensusVec>,
    pub total_cycles: u64,
    pub total_census: CensusVec,
}

fn to_cycles(ts: TimestampScalar) -> u64 {
    (ts - INITIAL_TIMESTAMP) / TIMESTAMP_STEP
}

fn prepare(
    bin: &[u32],
    text: &[u32],
) -> (Vec<Instruction>, RamWithRomRegion<ROM_SECOND_WORD_BITS>) {
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(text);
    let ram = RamWithRomRegion::<ROM_SECOND_WORD_BITS>::from_rom_content(bin, RAM_BOUND);
    (instructions, ram)
}

pub fn trace_verifier(bin: &[u32], text: &[u32], stream: Vec<u32>) -> Trace {
    let (instructions, mut ram) = prepare(bin, text);
    let tape = SimpleTape::new(&instructions);
    let mut state = State::initial_with_counters(CensusCounters::default());

    let cell = Rc::new(Cell::new((state.timestamp, state.counters)));
    let mut snapshotter = MarkingSnapshotter {
        cell: Rc::clone(&cell),
    };
    let mut nd = StampingSource {
        inner: QuasiUARTSource::new_with_reads(stream),
        cell: Rc::clone(&cell),
        marks: Vec::new(),
        census_marks: Vec::new(),
    };

    let finished = VM::<CensusCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        UNROLLED_RECURSION_CYCLES_BOUND,
        &mut nd,
    );
    assert!(finished, "verifier program must reach its end state");

    Trace {
        marks: nd.marks.into_iter().map(to_cycles).collect(),
        census_marks: nd.census_marks,
        total_cycles: to_cycles(state.timestamp),
        total_census: census_of(&state.counters),
    }
}

pub fn measure_verifier_cycles(bin: &[u32], text: &[u32], stream: Vec<u32>) -> u64 {
    let (instructions, mut ram) = prepare(bin, text);
    let tape = SimpleTape::new(&instructions);
    let mut state = State::initial_with_counters(DelegationsAndUnifiedCounters::default());
    let mut snapshotter =
        SimpleSnapshotter::<DelegationsAndUnifiedCounters, ROM_SECOND_WORD_BITS>::new_with_cycle_limit(
            UNROLLED_RECURSION_CYCLES_BOUND,
            state,
        );
    let mut nd = QuasiUARTSource::new_with_reads(stream);
    let finished = VM::<DelegationsAndUnifiedCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        UNROLLED_RECURSION_CYCLES_BOUND,
        &mut nd,
    );
    assert!(finished, "verifier program must reach its end state");
    to_cycles(state.timestamp)
}

pub fn fsv_dir() -> String {
    format!("{}/../tools/gkr_verifier", env!("CARGO_MANIFEST_DIR"))
}

fn read_compressed<T: serde::de::DeserializeOwned>(path: &str) -> T {
    use flate2::read::ZlibDecoder;
    use std::io::Read;

    let mut src = std::fs::File::open(path).unwrap_or_else(|e| panic!("open {path}: {e}"));
    let mut buffer = vec![];
    src.read_to_end(&mut buffer).expect("read fixture");
    let mut decoder = ZlibDecoder::new(&buffer[..]);
    let mut unpacked: Vec<u8> = vec![];
    decoder
        .read_to_end(&mut unpacked)
        .expect("decompress fixture");
    bincode::deserialize_from(&unpacked[..]).expect("deserialize fixture")
}

pub fn load_calibration_proof(name: &str) -> (Setups, ProgramProof) {
    let dir = std::env::var("COST_MODEL_FIXTURE_DIR").unwrap_or_else(|_| {
        panic!(
            "set COST_MODEL_FIXTURE_DIR to the directory holding \
             {name}_proof.bin / {name}_setups.bin (zlib-compressed bincode of \
             ProgramProof / Setups); see the module docs of \
             tests/cost_model_trace.rs for how to produce and name them"
        )
    });
    let proof = read_compressed(&format!("{dir}/{name}_proof.bin"));
    let setups = read_compressed(&format!("{dir}/{name}_setups.bin"));
    (setups, proof)
}
