use prover::common_constants::ROM_SECOND_WORD_BITS;
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::vm::DelegationsAndFamiliesCounters;
use riscv_transpiler::vm::SimpleSnapshotter;

pub type DecoderConfig = FullUnsignedMachineDecoderConfig;
pub type CountersT = DelegationsAndFamiliesCounters;
pub type Snapshotter = SimpleSnapshotter<CountersT, ROM_SECOND_WORD_BITS>;
