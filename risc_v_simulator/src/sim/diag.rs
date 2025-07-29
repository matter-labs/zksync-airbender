use crate::{
    abstractions::non_determinism::NonDeterminismCSRSource,
    cycle::{state::RiscV32ObservableState, MachineConfig},
    sim::RiscV32MachineSetup,
};
use std::{
    collections::HashMap,
    hash::Hasher,
    mem::size_of,
    path::{Path, PathBuf},
};

use addr2line::LookupContinuation;
use addr2line::{
    gimli::{
        self, CompleteLineProgram, EndianSlice, RunTimeEndian, SectionId, UnitOffset,
        UnitSectionOffset,
    },
    Context, Frame, LookupResult,
};
use cs::definitions::TimestampScalar;
use memmap2::Mmap;
use object::{File, Object, ObjectSection};

use crate::{
    abstractions::{mem_read, memory::MemorySource, tracer::Tracer},
    cycle::status_registers::TrapReason,
    mmu::MMUImplementation,
    qol::PipeOp as _,
};

use super::{RiscV32Machine, SimulatorConfig};

#[derive(Default, Debug, Clone)]
pub struct ProfilerStats {
    samples_success: usize,
    samples_failed: usize,
    samples_skipped: usize,
    samples_total: usize,
    samples_service: usize,
}

pub(crate) struct Profiler {
    // Safety: DwarfCache references data in symbol info.
    dwarf_cache: DwarfCache,
    symbol_info: SymbolInfo,
    output_path: PathBuf,
    frequency_recip: usize,
    reverse_graph: bool,
    pub stacktraces: StacktraceSet,
    pub stats: ProfilerStats,
}

impl Profiler {
    pub(crate) fn new(config: SimulatorConfig) -> Option<Self> {
        let dwarf_cache = DwarfCache {
            unit_data: HashMap::new(),
        };

        config.diagnostics.and_then(|d| {
            d.profiler_config.map(|p| Self {
                symbol_info: SymbolInfo::new(d.symbols_path),
                frequency_recip: p.frequency_recip,
                reverse_graph: p.reverse_graph,
                output_path: p.output_path,
                stacktraces: StacktraceSet::new(),
                dwarf_cache,
                stats: ProfilerStats::default(),
            })
        })
    }

    pub(crate) fn pre_cycle<S, C>(
        &mut self,
        machine: &mut S::M,
        // state: &RS,
        // memory_source: &mut MS,
        // memory_tracer: &mut TR,
        // mmu: &mut MMU,
        cycle: usize,
    ) where
        // RS: RiscV32Machine<ND, MS, C>,
        // ND: NonDeterminismCSRSource<MS>,
        // MS: MemorySource,
        // TR: Tracer<C>,
        // MMU: MMUImplementation<MS, TR, C>,
        C: MachineConfig,
        S: RiscV32MachineSetup,
    {
        if cycle % self.frequency_recip == 0 {
            self.stats.samples_total += 1;
            let st = machine.collect_stacktrace(&self.symbol_info, &mut self.dwarf_cache, cycle);
            // self.collect_stacktrace(state, memory_source, memory_tracer, mmu, cycle);
        }
    }

    fn collect_stacktrace<RS, ND, MS, TR, MMU, C>(
        &mut self,
        state: &RS,
        memory_source: &mut MS,
        memory_tracer: &mut TR,
        mmu: &mut MMU,
        cycle: usize,
    ) where
        RS: RiscV32Machine<ND, MS, TR, MMU, C>,
        ND: NonDeterminismCSRSource<MS>,
        MS: MemorySource,
        TR: Tracer<C>,
        MMU: MMUImplementation<MS, TR, C>,
        C: MachineConfig,
    {
        self.stats.samples_total += 1;

        let symbol_info = &self.symbol_info;

        let mut callstack = Vec::with_capacity(6);

        // Current frame
        callstack.push(state.state().pc as u64);

        let mut fp = state.state().registers[8];

        if fp == 0 {
            self.stats.samples_skipped += 1;
            return;
        }

        loop {
            let mut trap = TrapReason::NoTrap;

            let fpp = mmu.map_virtual_to_physical(
                fp,
                crate::cycle::state::Mode::Machine,
                crate::abstractions::memory::AccessType::MemLoad,
                memory_source,
                memory_tracer,
                &mut trap,
            );

            // TODO: remove once the issue with non complying functions is solved.
            if fpp < 8 {
                break;
            }

            let addr = mem_read::<_, _, _>(
                memory_source,
                memory_tracer,
                fpp - 4,
                size_of::<u32>() as u32,
                crate::abstractions::memory::AccessType::MemLoad,
                &mut trap,
            );

            let next = mem_read::<_, _, _>(
                memory_source,
                memory_tracer,
                fpp - 8,
                size_of::<u32>() as u32,
                crate::abstractions::memory::AccessType::MemLoad,
                &mut trap,
            );

            // TODO: Remove once the issue with non complying functions is solved.
            if addr < 4 {
                break;
            }
            if next as u64 == fpp {
                break;
            }
            if addr == 0 {
                break;
            }

            // Subbing one instruction because the frame's return address point to instruction
            // that follows the call, not the call itself. In case of inlining this can be
            // several frames away.
            let addr = addr - 4;

            callstack.push(addr as u64);

            fp = next;
        }

        let mut stackframes = Vec::with_capacity(8);

        for (i, addr) in callstack.iter().enumerate() {
            let r = symbol_info.get_address_frames(&mut self.dwarf_cache, *addr);

            let (frames, section_offset) = match r {
                Some(r) => r,
                // None if stackframes.len() != 0 => panic!("Non top frame couldn't be retrieved."),
                None => break,
            };

            for frame in frames {
                let offset = frame.dw_die_offset.unwrap();
                stackframes.push(FrameKey {
                    section_offset,
                    unit_offset: offset,
                });

                if i == 0
                    && false
                        == symbol_info.is_address_traceable(
                            &self.dwarf_cache,
                            state.state().pc as u64,
                            &frame,
                        )
                {
                    // We're in a service code.
                    self.stats.samples_service += 1;
                    return;
                }
            }
        }

        if stackframes.len() == 0 {
            self.stats.samples_failed += 1;
            return;
        }
        self.stats.samples_success += 1;

        let stacktrace = Stacktrace::new(stackframes);

        self.stacktraces.absorb(stacktrace);
    }

    pub(crate) fn write_stacktrace(&self) {
        let file = match std::fs::File::create(&self.output_path) {
            Err(why) => panic!("couldn't create file {}", why),
            Ok(file) => file,
        };

        let mut mapped = Vec::with_capacity(self.stacktraces.traces.len());

        for (st, c) in &self.stacktraces.traces {
            let names = st
                .frames
                .iter()
                .rev()
                .map(|frame| {
                    self.dwarf_cache
                        .unit_data
                        .get(&frame.section_offset)
                        .unwrap()
                        .frames
                        .get(&frame.unit_offset)
                        .unwrap()
                        .name
                        .as_str()
                })
                .collect::<Vec<_>>();
            names
                .join(";")
                .op(|x| format!("{} {}", x, c).to_owned().to(|x| mapped.push(x)));
        }

        let mut opts = inferno::flamegraph::Options::default();

        opts.reverse_stack_order = self.reverse_graph;

        inferno::flamegraph::from_lines(&mut opts, mapped.iter().map(|x| x.as_str()), file)
            .unwrap();
    }

    pub(crate) fn print_stats(&self) {
        println!("{:#?}", self.stats);
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct FrameKey {
    section_offset: UnitSectionOffset,
    unit_offset: UnitOffset<usize>,
}

#[derive(Debug)]
struct FrameInfo {
    // Address of one instruction beyond last the prologue instruction.
    prologue_end: u64,
    // Address of the first epilogue instruction.
    epilogue_begin: u64,
    #[allow(dead_code)]
    no_return: bool,
    #[allow(dead_code)]
    is_inlined: bool,
    is_tracked: bool,
    name: String,
}

struct UnitInfo<'a> {
    line_program_complete: CompleteLineProgram<EndianSlice<'a, RunTimeEndian>, usize>,
    line_sequences: Vec<gimli::LineSequence<EndianSlice<'a, RunTimeEndian>>>,
    frames: HashMap<UnitOffset<usize>, FrameInfo>,
}

pub(crate) struct DwarfCache {
    unit_data: HashMap<UnitSectionOffset, UnitInfo<'static>>,
}

#[allow(dead_code)] // Struct has data dependencies
pub(crate) struct SymbolInfo {
    // Safety: Values must be dropped in the dependency order.
    ctx: Context<EndianSlice<'static, RunTimeEndian>>,
    object: object::File<'static>,
    // Holds the slice that all above fields reference.
    mmap: Mmap,
}

impl SymbolInfo {
    fn new<P: AsRef<Path>>(path: P) -> Self {
        let x = std::fs::File::open(path).unwrap();
        let mmap = unsafe { memmap2::Mmap::map(&x).unwrap() };

        // Safety: map contains a raw pointer, so it is safe to move.
        let object = object::File::parse(&*mmap).unwrap();
        let object = unsafe { std::mem::transmute::<_, File<'static>>(object) };

        let endian = match object.is_little_endian() {
            true => RunTimeEndian::Little,
            false => RunTimeEndian::Big,
        };

        let load_section = |id: SectionId| -> Result<_, ()> {
            let name = id.name();

            match object.section_by_name(name) {
                Some(section) => match section.uncompressed_data().unwrap() {
                    std::borrow::Cow::Borrowed(section) => Ok(EndianSlice::new(section, endian)),
                    std::borrow::Cow::Owned(_) => {
                        unreachable!("We're following the borrowed path.")
                    }
                },
                None => Ok(EndianSlice::new(&[][..], endian)),
            }
        };

        let dwarf = addr2line::gimli::Dwarf::load(load_section)
            .expect("Debug symbols could not be loaded.");

        let ctx = Context::from_dwarf(dwarf).unwrap();

        SymbolInfo { mmap, object, ctx }
    }

    fn is_address_traceable(
        &self,
        cache: &DwarfCache,
        address: u64,
        frame: &Frame<'_, EndianSlice<'_, RunTimeEndian>>,
    ) -> bool {
        let (_dw, unit) = self
            .ctx
            .find_dwarf_and_unit(address)
            .skip_all_loads()
            .expect("Frame existence implies unit.");

        let mut tracked = false;

        let r = cache
            .unit_data
            .get(&unit.header.offset())
            .expect("Unit info should've been created on frame loading.")
            .frames
            .get(&frame.dw_die_offset.unwrap())
            .expect("Frame info should've been created on frame loading.")
            .to(|x| {
                if x.is_tracked {
                    println!("is_traceable:");
                    println!("address: 0x{:08x}", address);
                    println!("address: {}", address);
                    println!("{:#?}", x);
                    tracked = true;
                }
                address >= x.prologue_end && address < x.epilogue_begin
            });

        if tracked {
            println!("r {}", r);
        }

        r
    }

    #[allow(dead_code)]
    /// Prints a bunch of info about a frame to console.
    fn inspect_frame(&self, address: u64, frame: &Frame<'_, EndianSlice<'_, RunTimeEndian>>) {
        let x = self.ctx.find_dwarf_and_unit(address).skip_all_loads();
        if x.is_none() {
            return;
        }

        let (dw, unit) = x.unwrap();

        let mut cursor = unit
            .entries_at_offset(frame.dw_die_offset.unwrap())
            .unwrap();
        cursor.next_entry().unwrap();
        let die = cursor.current().unwrap();

        let tag_n = match die.tag() {
            gimli::DW_TAG_subprogram => "DW_TAG_subprogram".to_owned(),
            gimli::DW_TAG_inlined_subroutine => "DW_TAG_inlined_subroutine".to_owned(),
            gimli::DW_TAG_variable => "DW_TAG_variable".to_owned(),
            gimli::DW_TAG_formal_parameter => "DW_TAG_formal_parameter".to_owned(),
            otherwise => format!("{:x?}", otherwise),
        };
        println!("tag {:?}", tag_n);

        let mut attrs = die.attrs();

        while let Ok(Some(attr)) = attrs.next() {
            println!("   {:x?} -> {:x?}", attr.name(), attr.value());

            match attr.name() {
                gimli::DW_AT_linkage_name | gimli::DW_AT_name => {
                    let n = attr.value();

                    match n {
                        gimli::AttributeValue::DebugStrRef(n) => {
                            let s = dw.string(n).unwrap();
                            println!("      value: {}", s.to_string_lossy());
                        }
                        _ => {}
                    }
                }

                gimli::DW_AT_frame_base => match attr.value() {
                    gimli::AttributeValue::Exprloc(ex) => {
                        println!("expr decode");
                        let mut ops = ex.operations(unit.encoding());

                        while let Ok(Some(op)) = ops.next() {
                            println!("op: {:?}", op);
                        }
                    }
                    _ => {}
                },
                gimli::DW_AT_specification | gimli::DW_AT_abstract_origin => match attr.value() {
                    gimli::AttributeValue::UnitRef(other_offset) => {
                        let mut cursor = unit.entries_at_offset(other_offset).unwrap();
                        cursor.next_entry().unwrap();
                        let die2 = cursor.current().unwrap();

                        let mut attrs = die2.attrs();

                        while let Ok(Some(attr)) = attrs.next() {
                            println!("      {:x?} -> {:x?}", attr.name(), attr.value());

                            match attr.name() {
                                gimli::DW_AT_linkage_name | gimli::DW_AT_name => {
                                    let n = attr.value();

                                    match n {
                                        gimli::AttributeValue::DebugStrRef(n) => {
                                            let s = dw.string(n).unwrap();
                                            println!("         value: {}", s.to_string_lossy());
                                        }
                                        _ => {}
                                    }
                                }
                                _ => {}
                            };
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        let (line_program, sequences) = unit
            .line_program
            .clone()
            .unwrap()
            .clone()
            .sequences()
            .unwrap();

        for s in sequences {
            if address >= s.start && address < s.end {
                println!("found seq: {:x} -> {:x}", s.start, s.end);

                let mut sm = line_program.resume_from(&s);

                while let Ok(Some((_h, r))) = sm.next_row() {
                    let line_num = match r.line() {
                        Some(r) => r.get(),
                        None => 0,
                    };
                    println!(
                        "row addr {:08x}, line {}, stmt {}, prol_end {}, epi_start {},",
                        r.address(),
                        line_num,
                        r.is_stmt(),
                        r.prologue_end(),
                        r.epilogue_begin()
                    );
                }
            }
        }
    }

    fn get_address_frames<'a>(
        &'a self,
        cache: &mut DwarfCache,
        address: u64,
    ) -> Option<(
        Vec<Frame<'a, EndianSlice<'a, RunTimeEndian>>>,
        UnitSectionOffset,
    )> {
        let (_dw, unit, unit_info) =
            if let Some((dw, unit)) = self.ctx.find_dwarf_and_unit(address).skip_all_loads() {
                let unit_locator = unit.header.offset();

                let unit_info = cache.unit_data.entry(unit_locator).or_insert_with(|| {
                    let (line_program, sequences) = unit
                        .line_program
                        .clone()
                        .unwrap()
                        .clone()
                        .sequences()
                        .unwrap();

                    UnitInfo {
                        line_program_complete: line_program,
                        line_sequences: sequences,
                        frames: HashMap::new(),
                    }
                });

                (dw, unit, unit_info)
            } else {
                return None;
            };

        let mut frames = self.ctx.find_frames(address);

        let mut frames = loop {
            match frames {
                LookupResult::Output(r) => break r,
                LookupResult::Load {
                    load: _,
                    continuation,
                } => {
                    // Not using split DWARF.
                    frames = continuation.resume(None);
                }
            }
        }
        .unwrap();

        let mut result = Vec::with_capacity(8);

        while let Ok(Some(frame)) = frames.next() {
            let mut tracked = false;

            if false
                && frame
                    .function
                    .as_ref()
                    .unwrap()
                    .demangle()
                    .unwrap()
                    .contains("talc::talc::Talc<O>::malloc")
            {
                tracked = true;
                // panic!("found!!!!!! {}", frame.function.as_ref().unwrap().demangle().unwrap());
            }

            unit_info
                .frames
                .entry(frame.dw_die_offset.unwrap())
                .or_insert_with(|| {
                    let sequence = &unit_info.line_sequences;
                    for s in sequence {
                        if address >= s.start && address < s.end {
                            let mut sm = unit_info.line_program_complete.resume_from(&s);

                            let mut prologue_end = None;
                            let mut epilogue_begin = None;
                            let mut no_return = false;
                            let mut is_inlined = false;

                            while let Ok(Some((_h, r))) = sm.next_row() {
                                assert!(r.address() <= s.end);

                                if r.prologue_end() {
                                    prologue_end = Some(r.address())
                                }
                                if r.epilogue_begin() {
                                    epilogue_begin = Some(r.address())
                                }
                            }

                            let cursor = unit
                                .entries_at_offset(frame.dw_die_offset.unwrap())
                                .unwrap()
                                .op(|x| {
                                    x.next_entry()
                                        .expect("A unit must exist at the provided offset.");
                                });

                            let die = cursor.current().unwrap();

                            match die.tag() {
                                gimli::DW_TAG_inlined_subroutine => is_inlined = true,
                                _ => (),
                            }

                            let mut attrs = die.attrs();

                            while let Ok(Some(attr)) = attrs.next() {
                                match attr.name() {
                                    gimli::DW_AT_noreturn if epilogue_begin.is_some() => {
                                        panic!("Non returning functions shouln't have an epilogue.")
                                    }
                                    gimli::DW_AT_noreturn => no_return = true,
                                    _ => (),
                                }
                            }

                            let r = FrameInfo {
                                prologue_end: prologue_end.expect(
                                    format!("A function must have a prologue. 0x{:08x}", address)
                                        .as_str(),
                                ),
                                epilogue_begin: epilogue_begin.unwrap_or_else(|| u64::MAX),
                                no_return,
                                is_inlined,
                                is_tracked: tracked,
                                name: frame
                                    .function
                                    .as_ref()
                                    .unwrap()
                                    .demangle()
                                    .unwrap()
                                    .to_string(),
                            };

                            if tracked {
                                println!("{:#?}", r);
                            }

                            return r;
                        }
                    }

                    panic!(
                        "An line sequence was not found for frame {:?}, addr {}",
                        frame.function.as_ref().unwrap().demangle(),
                        address
                    );
                });

            // Safety: The borrow checker assumes that the frame lives for 'const (derived from
            // `ctx` field in `Self`). The actual lifetime is the lifetime of `self`. So we're
            // adjusting the lifetime args in the return type accordingly.
            unsafe { result.push(std::mem::transmute(frame)) };
        }

        Some((result, unit.header.offset()))
    }
}

#[derive(Debug)]
struct Stacktrace {
    frames: Vec<FrameKey>,
}

impl std::cmp::PartialEq for Stacktrace {
    fn eq(&self, other: &Self) -> bool {
        self.frames == other.frames
    }
}

impl std::cmp::Eq for Stacktrace {}

impl std::hash::Hash for Stacktrace {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for frame in &self.frames {
            frame.hash(state);
        }
    }
}

impl Stacktrace {
    pub(crate) fn new(frames: Vec<FrameKey>) -> Self {
        assert_ne!(0, frames.len());
        Self { frames }
    }
}

pub(crate) enum StacktraceCollectionResult {
    UserCode(Stacktrace),
    ServiceCode,
    Skipped,
    Failed,
}

#[derive(Debug)]
pub(crate) struct StacktraceSet {
    traces: HashMap<Stacktrace, usize>,
}

impl StacktraceSet {
    fn new() -> Self {
        Self {
            traces: HashMap::new(),
        }
    }

    fn absorb(&mut self, stacktrace: Stacktrace) {
        self.traces
            .entry(stacktrace)
            .and_modify(|x| *x += 1)
            .or_insert(1);
    }
}

pub(crate) fn collect_stacktrace<MS, TR, MMU, C>(
    symbol_info: &SymbolInfo,
    dwarf_cache: &mut DwarfCache,
    state: &RiscV32ObservableState,
    memory_source: &mut MS,
    memory_tracer: &mut TR,
    mmu: &mut MMU,
    cycle: usize,
) -> StacktraceCollectionResult
where
    MS: MemorySource,
    TR: Tracer<C>,
    MMU: MMUImplementation<MS, TR, C>,
    C: MachineConfig,
{
    let mut callstack = Vec::with_capacity(6);

    // Current frame
    callstack.push(state.pc as u64);

    let mut fp = state.registers[8];

    if fp == 0 {
        // self.stats.samples_skipped += 1;
        return StacktraceCollectionResult::Skipped;
    }

    loop {
        let mut trap = TrapReason::NoTrap;

        let fpp = mmu.map_virtual_to_physical(
            fp,
            crate::cycle::state::Mode::Machine,
            crate::abstractions::memory::AccessType::MemLoad,
            memory_source,
            memory_tracer,
            &mut trap,
        );

        // TODO: remove once the issue with non complying functions is solved.
        if fpp < 8 {
            break;
        }

        let addr = mem_read::<_, _, _>(
            memory_source,
            memory_tracer,
            fpp - 4,
            size_of::<u32>() as u32,
            crate::abstractions::memory::AccessType::MemLoad,
            &mut trap,
        );

        let next = mem_read::<_, _, _>(
            memory_source,
            memory_tracer,
            fpp - 8,
            size_of::<u32>() as u32,
            crate::abstractions::memory::AccessType::MemLoad,
            &mut trap,
        );

        // TODO: Remove once the issue with non complying functions is solved.
        if addr < 4 {
            break;
        }
        if next as u64 == fpp {
            break;
        }
        if addr == 0 {
            break;
        }

        // Subbing one instruction because the frame's return address point to instruction
        // that follows the call, not the call itself. In case of inlining this can be
        // several frames away.
        let addr = addr - 4;

        callstack.push(addr as u64);

        fp = next;
    }

    let mut stackframes = Vec::with_capacity(8);

    for (i, addr) in callstack.iter().enumerate() {
        let r = symbol_info.get_address_frames(dwarf_cache, *addr);

        let (frames, section_offset) = match r {
            Some(r) => r,
            // None if stackframes.len() != 0 => panic!("Non top frame couldn't be retrieved."),
            None => break,
        };

        for frame in frames {
            let offset = frame.dw_die_offset.unwrap();
            stackframes.push(FrameKey {
                section_offset,
                unit_offset: offset,
            });

            if i == 0
                && false == symbol_info.is_address_traceable(dwarf_cache, state.pc as u64, &frame)
            {
                // We're in a service code.
                // self.stats.samples_service += 1;
                return StacktraceCollectionResult::ServiceCode;
            }
        }
    }

    if stackframes.len() == 0 {
        // self.stats.samples_failed += 1;
        return StacktraceCollectionResult::Failed;
    }
    // self.stats.samples_success += 1;

    let stacktrace = Stacktrace::new(stackframes);

    StacktraceCollectionResult::UserCode(stacktrace)

    // self.stacktraces.absorb(stacktrace);
}
