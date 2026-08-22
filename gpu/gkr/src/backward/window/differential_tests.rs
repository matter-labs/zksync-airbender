//! Differential for the windowed R0 arm: the window executor plus the
//! TensorRoundTail against a host model of the same program.
//!
//! The model is written from the CONVENTION the two arms have to share, not
//! from the kernel:
//!
//! * The per-round arm folds adjacent rows (`s0 = V[2 * row]`,
//!   `s1 = V[2 * row + 1]`) and round `r` uses claim-point coordinate `r`, so
//!   round `r` binds trace-row bit `r`. Tensor axis `r` is therefore trace-row
//!   bit `r`, and the window's own `x2` — the corner's LOW bit, the axis the R0
//!   program's quadratic term is taken over — is tensor axis 0.
//! * A linear atom contributes its source's multilinear extension over the
//!   three peeled bits. The Boolean corners of that source already carry the
//!   whole expression's value, products included, so a product atom contributes
//!   only the EXCESS of the true product over its own multilinear
//!   interpolation: zero on the Boolean cube, the product of the two factors'
//!   endpoint differences wherever an axis is the infinity endpoint.
//!
//! Both statements were wrong in the first integration and both are wrong in a
//! way that only shows up past round 0, which is why the model derives them
//! rather than mirroring the executor.

use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::backward::window::{
    WINDOW_OPCODE_GROUP_BF, WINDOW_OPCODE_GROUP_E4, WINDOW_OPCODE_LINEAR_BF_PROCEDURAL,
    WINDOW_OPCODE_LINEAR_E4_WIDE, WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB,
    WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B, WINDOW_OPCODE_PRODUCT_E4_E4,
};
use gpu_gkr_compiler::{
    ImmediateId, WindowCapacities, WindowProgram, WindowShape, WindowSourceLane,
    WINDOW_SECTION_WORDS,
};
use gpu_prover_context::ProverContext;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use super::binding::{
    build_window_binding, resolve_window_kernel, window_partials_len, window_row_tiles,
    WindowAddressing, WindowLaunch, WindowRuntimeScratch,
};
use super::generated_registry::{
    WINDOWED_R0_DISPATCH, WINDOWED_R0_FALLBACK_MASK, WINDOWED_R0_KERNELS,
};
use super::reference::tensor_round_tail_reference;
use super::tail::{
    launch_window_tensor_round_tail, WindowTailArm, WindowTailState, WINDOW_TAIL_TENSOR_CELLS,
};
use crate::backward::kernels::{
    get_eq_high_constant_device_ptr, launch_build_eq_high_and_low_groups_from_point,
    resolve_active_eq_slot, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
use crate::backward::vm::seg::bwd_seg_coeff_bank_device_ptr;
use crate::backward::vm::seg_desc::{
    BwdSegAddrSlot, BWD_COEFF_ORIGIN_READ_BASE, BWD_COEFF_ORIGIN_READ_EXT,
    BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW, BWD_COEFF_PROCEDURAL_NONE,
    BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS, BWD_SEG_ADDR_COLUMN_BITS, BWD_SEG_OUTPUT_BANK,
};
use crate::backward::{make_eq_sizes, GkrEqSizes};
use crate::test_utils::make_test_context;
use crate::upstream::{Field, FieldExtension, PrimeField};

/// Coordinates one window peels.
const PEELED: usize = 3;
/// Bank slots the fixtures draw cores from; slots 0 and 1 stay the reserved
/// literals so a wire that names them keeps its production meaning.
const FIRST_CORE_SLOT: usize = 2;

// ── Field helpers ────────────────────────────────────────────────────────────

fn add(mut left: E4, right: E4) -> E4 {
    left.add_assign(&right);
    left
}

fn sub(mut left: E4, right: E4) -> E4 {
    left.sub_assign(&right);
    left
}

fn mul(mut left: E4, right: E4) -> E4 {
    left.mul_assign(&right);
    left
}

fn scale(mut value: E4, by: BF) -> E4 {
    value.mul_assign_by_base(&by);
    value
}

fn lift(value: BF) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(value)
}

fn point(value: usize) -> E4 {
    lift(BF::from_u32_with_reduction(value as u32))
}

fn halve(mut value: E4) -> E4 {
    let half = BF::from_u32_with_reduction(2)
        .inverse()
        .expect("two is invertible");
    value.mul_assign_by_base(&half);
    value
}

/// Leading coefficient of the quadratic through samples at `0, 1, 2`.
fn leading(samples: [E4; 3]) -> E4 {
    halve(add(
        sub(samples[2], add(samples[1], samples[1])),
        samples[0],
    ))
}

fn random_bf(rng: &mut StdRng) -> BF {
    BF::from_u32_with_reduction(rng.random())
}

fn random_e4(rng: &mut StdRng) -> E4 {
    E4::from_array_of_base(std::array::from_fn(|_| random_bf(rng)))
}

fn basis(limb: usize) -> E4 {
    E4::from_array_of_base(std::array::from_fn(|index| {
        if index == limb {
            BF::ONE
        } else {
            BF::ZERO
        }
    }))
}

// ── The program the fixture builds ───────────────────────────────────────────

/// A source operand: a matrix column, or a virtual-setup kind the wire carries
/// by value.
#[derive(Clone, Copy)]
enum Source {
    Base(usize),
    Ext(usize),
    Procedural(u8),
}

/// A term inside a BF group, or a standalone BF atom.
#[derive(Clone, Copy)]
enum Term {
    Linear(Source),
    Product(Source, Source),
}

#[derive(Clone)]
enum Atom {
    /// A standalone BF-section term with its own bank core.
    Bf { core: usize, term: Term },
    /// A BF group: one core, `product_prefix` products then an optional linear
    /// tail, each member scaled by a wire immediate.
    BfGroup {
        core: usize,
        product_prefix: usize,
        members: Vec<(BF, Term)>,
    },
    /// The wide linear-E4 form: four consecutive basis-scaled bank slots.
    LinearExt { core: usize, column: usize },
    /// An E4-section product with its own core, optionally negated.
    ExtSingleton {
        core: usize,
        negate: bool,
        term: Term,
    },
    /// An E4 fixed pair: one core, two same-class products.
    ExtPair {
        core: usize,
        members: [(bool, Term); 2],
    },
}

/// Which E4-section product class a term encodes.
fn ext_product_opcode(term: Term) -> u16 {
    match term {
        Term::Product(Source::Base(_), Source::Ext(_)) => 3,
        Term::Product(Source::Ext(_), Source::Ext(_)) => WINDOW_OPCODE_PRODUCT_E4_E4,
        _ => panic!("not an E4-section product"),
    }
}

fn immediate_word(value: BF, immediates: &mut Vec<u32>) -> u16 {
    if value == BF::ONE {
        return ImmediateId::ONE.0;
    }
    let mut negative_one = BF::ONE;
    negative_one.negate();
    if value == negative_one {
        return ImmediateId::NEG_ONE.0;
    }
    let raw = value.as_u32_raw_repr_reduced();
    let index = immediates
        .iter()
        .position(|entry| *entry == raw)
        .unwrap_or({
            immediates.push(raw);
            immediates.len() - 1
        });
    ImmediateId::RESERVED + index as u16
}

/// The fixture's own source table: one addressing slot per matrix, one source
/// id per column, and the lane words the binder rewrites.
struct Sources {
    slots: Vec<BwdSegAddrSlot>,
    lanes: Vec<Option<u16>>,
    ids: BTreeMap<(bool, usize), u16>,
}

impl Sources {
    fn lane(slot: usize, column: usize) -> u16 {
        ((slot << BWD_SEG_ADDR_COLUMN_BITS) | column) as u16
    }

    /// The source id of one column, interned on first use.
    fn id(&mut self, extension: bool, column: usize) -> u16 {
        let next = self.lanes.len() as u16;
        *self.ids.entry((extension, column)).or_insert_with(|| {
            let slot = usize::from(extension);
            self.lanes.push(Some(Self::lane(slot, column)));
            next
        })
    }
}

/// Encode one atom list into the four sections, recording the lane words.
fn encode(
    atoms: &[Atom],
    sources: &mut Sources,
    immediates: &mut Vec<u32>,
) -> (Vec<u16>, Vec<WindowSourceLane>, [u32; WINDOW_SECTION_WORDS]) {
    let mut sections: [Vec<u16>; 4] = Default::default();
    let mut lanes: [Vec<WindowSourceLane>; 4] = Default::default();

    // One term instruction, registering the lane words its addressed operands
    // occupy. A procedural operand carries its KIND in the word and is never a
    // lane, exactly as `window_operand_words` encodes it.
    let push = |section: usize,
                sections: &mut [Vec<u16>; 4],
                lanes: &mut [Vec<WindowSourceLane>; 4],
                sources: &mut Sources,
                opcode: u16,
                factor: u16,
                operands: [Option<Source>; 2]| {
        let record = sections[section].len() as u32;
        let mut words = [opcode, factor, 0, 0];
        for (index, operand) in operands.into_iter().enumerate() {
            match operand {
                None => {}
                Some(Source::Procedural(kind)) => words[2 + index] = u16::from(kind),
                Some(Source::Base(column)) => {
                    let source = sources.id(false, column);
                    lanes[section].push(WindowSourceLane {
                        word: record + 2 + index as u32,
                        source,
                    });
                }
                Some(Source::Ext(column)) => {
                    let source = sources.id(true, column);
                    lanes[section].push(WindowSourceLane {
                        word: record + 2 + index as u32,
                        source,
                    });
                }
            }
        }
        sections[section].extend(words);
    };

    let term_operands = |term: Term| match term {
        Term::Linear(a) => [Some(a), None],
        Term::Product(a, b) => [Some(a), Some(b)],
    };
    let bf_term_opcode = |term: Term| match term {
        Term::Linear(Source::Procedural(_)) => WINDOW_OPCODE_LINEAR_BF_PROCEDURAL,
        Term::Linear(_) => 0,
        Term::Product(Source::Procedural(_), Source::Procedural(_)) => {
            WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB
        }
        Term::Product(_, Source::Procedural(_)) => WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B,
        Term::Product(..) => 2,
    };

    for atom in atoms {
        match atom {
            Atom::Bf { core, term } => push(
                0,
                &mut sections,
                &mut lanes,
                sources,
                bf_term_opcode(*term),
                *core as u16,
                term_operands(*term),
            ),
            Atom::BfGroup {
                core,
                product_prefix,
                members,
            } => {
                push(
                    0,
                    &mut sections,
                    &mut lanes,
                    sources,
                    WINDOW_OPCODE_GROUP_BF,
                    *core as u16,
                    [None, None],
                );
                // The header's arity and product prefix ride the operand words
                // the wire reserves for them.
                let header = sections[0].len() - 2;
                sections[0][header] = members.len() as u16;
                sections[0][header + 1] = *product_prefix as u16 | 0x8000;
                for (index, (immediate, term)) in members.iter().enumerate() {
                    let mut factor = immediate_word(*immediate, immediates);
                    // A mid-prefix reduction every four products, the same rule
                    // the lowering applies.
                    if index < *product_prefix
                        && (index + 1) % 4 == 0
                        && index + 1 < *product_prefix
                    {
                        factor |= 0x8000;
                    }
                    push(
                        0,
                        &mut sections,
                        &mut lanes,
                        sources,
                        bf_term_opcode(*term),
                        factor,
                        term_operands(*term),
                    );
                }
            }
            Atom::LinearExt { core, column } => push(
                1,
                &mut sections,
                &mut lanes,
                sources,
                WINDOW_OPCODE_LINEAR_E4_WIDE,
                *core as u16,
                [Some(Source::Ext(*column)), None],
            ),
            Atom::ExtSingleton { core, negate, term } => push(
                2,
                &mut sections,
                &mut lanes,
                sources,
                ext_product_opcode(*term),
                *core as u16 | if *negate { 0x8000 } else { 0 },
                term_operands(*term),
            ),
            Atom::ExtPair { core, members } => {
                push(
                    3,
                    &mut sections,
                    &mut lanes,
                    sources,
                    WINDOW_OPCODE_GROUP_E4,
                    *core as u16,
                    [None, None],
                );
                for (negate, term) in members {
                    let mut negative_one = BF::ONE;
                    negative_one.negate();
                    let immediate = if *negate { negative_one } else { BF::ONE };
                    push(
                        3,
                        &mut sections,
                        &mut lanes,
                        sources,
                        ext_product_opcode(*term),
                        immediate_word(immediate, immediates),
                        term_operands(*term),
                    );
                }
            }
        }
    }

    let mut words = Vec::new();
    let mut source_lanes = Vec::new();
    let mut endpoints = [0u32; WINDOW_SECTION_WORDS];
    for (section, (section_words, section_lanes)) in
        sections.into_iter().zip(lanes.into_iter()).enumerate()
    {
        let base = words.len() as u32;
        source_lanes.extend(section_lanes.into_iter().map(|lane| WindowSourceLane {
            word: lane.word + base,
            source: lane.source,
        }));
        words.extend(section_words);
        endpoints[section] = words.len() as u32 / 4;
    }
    source_lanes.sort_by_key(|lane| lane.word);
    (words, source_lanes, endpoints)
}

// ── The host model ───────────────────────────────────────────────────────────

/// The fixture's device state plus the host copies the model reads.
struct Fixture {
    trace_len: usize,
    base: Vec<BF>,
    ext: Vec<E4>,
    bank: Vec<E4>,
    claim_point: Vec<E4>,
}

impl Fixture {
    fn rows(&self) -> usize {
        self.trace_len >> PEELED
    }

    fn corner(&self, row: usize, bits: [usize; PEELED]) -> usize {
        (row << PEELED) | bits[0] | (bits[1] << 1) | (bits[2] << 2)
    }

    fn source_corner(&self, source: Source, index: usize) -> E4 {
        match source {
            Source::Base(column) => lift(self.base[column * self.trace_len + index]),
            Source::Ext(column) => self.ext[column * self.trace_len + index],
            Source::Procedural(kind) => lift(procedural_value(kind, index)),
        }
    }

    /// The multilinear extension of one source over the three peeled bits.
    fn extension(&self, source: Source, row: usize, at: [E4; PEELED]) -> E4 {
        self.combine(row, at, |fixture, index| {
            fixture.source_corner(source, index)
        })
    }

    /// The multilinear extension of the pointwise product of two sources — the
    /// interpolation a materialized column would carry.
    fn product_extension(&self, a: Source, b: Source, row: usize, at: [E4; PEELED]) -> E4 {
        self.combine(row, at, |fixture, index| {
            mul(
                fixture.source_corner(a, index),
                fixture.source_corner(b, index),
            )
        })
    }

    fn combine(&self, row: usize, at: [E4; PEELED], corner: impl Fn(&Self, usize) -> E4) -> E4 {
        let mut total = E4::ZERO;
        for mask in 0..1usize << PEELED {
            let bits = [mask & 1, (mask >> 1) & 1, (mask >> 2) & 1];
            let mut weight = E4::ONE;
            for (axis, bit) in bits.iter().enumerate() {
                weight = mul(
                    weight,
                    if *bit == 1 {
                        at[axis]
                    } else {
                        sub(E4::ONE, at[axis])
                    },
                );
            }
            total = add(total, mul(weight, corner(self, self.corner(row, bits))));
        }
        total
    }

    /// One term's value at `at`: a linear term is its source's extension; a
    /// product term is the EXCESS of the true product over its multilinear
    /// interpolation.
    fn term(&self, term: Term, row: usize, at: [E4; PEELED]) -> E4 {
        match term {
            Term::Linear(source) => self.extension(source, row, at),
            Term::Product(a, b) => sub(
                mul(self.extension(a, row, at), self.extension(b, row, at)),
                self.product_extension(a, b, row, at),
            ),
        }
    }

    fn atom(&self, atom: &Atom, row: usize, at: [E4; PEELED]) -> E4 {
        match atom {
            Atom::Bf { core, term } => mul(self.bank[*core], self.term(*term, row, at)),
            Atom::BfGroup { core, members, .. } => {
                let sum = members.iter().fold(E4::ZERO, |sum, (immediate, term)| {
                    add(sum, scale(self.term(*term, row, at), *immediate))
                });
                mul(self.bank[*core], sum)
            }
            Atom::LinearExt { core, column } => mul(
                self.bank[*core],
                self.extension(Source::Ext(*column), row, at),
            ),
            Atom::ExtSingleton { core, negate, term } => {
                let value = mul(self.bank[*core], self.term(*term, row, at));
                if *negate {
                    sub(E4::ZERO, value)
                } else {
                    value
                }
            }
            Atom::ExtPair { core, members } => {
                let sum = members.iter().fold(E4::ZERO, |sum, (negate, term)| {
                    let value = self.term(*term, row, at);
                    if *negate {
                        sub(sum, value)
                    } else {
                        add(sum, value)
                    }
                });
                mul(self.bank[*core], sum)
            }
        }
    }

    /// The equality weight of one surviving row: claim-point coordinate `3 + i`
    /// against row bit `i`.
    fn row_weight(&self, row: usize) -> E4 {
        let bits = self.trace_len.trailing_zeros() as usize - PEELED;
        (0..bits).fold(E4::ONE, |weight, bit| {
            let coordinate = self.claim_point[PEELED + bit];
            mul(
                weight,
                if (row >> bit) & 1 == 1 {
                    coordinate
                } else {
                    sub(E4::ONE, coordinate)
                },
            )
        })
    }

    /// The 27-cell tensor on `{0, 1, infinity}^3`, axis `r` = trace-row bit `r`.
    fn tensor(&self, atoms: &[Atom]) -> [E4; 27] {
        let mut finite = [E4::ZERO; 27];
        for row in 0..self.rows() {
            let weight = self.row_weight(row);
            for a0 in 0..3 {
                for a1 in 0..3 {
                    for a2 in 0..3 {
                        let at = [point(a0), point(a1), point(a2)];
                        let value = atoms
                            .iter()
                            .fold(E4::ZERO, |sum, atom| add(sum, self.atom(atom, row, at)));
                        let cell = 9 * a0 + 3 * a1 + a2;
                        finite[cell] = add(finite[cell], mul(weight, value));
                    }
                }
            }
        }
        let mut tensor = finite;
        for axis in 0..PEELED {
            for first in 0..3 {
                for second in 0..3 {
                    let index = |coordinate: usize| match axis {
                        0 => 9 * coordinate + 3 * first + second,
                        1 => 9 * first + 3 * coordinate + second,
                        _ => 9 * first + 3 * second + coordinate,
                    };
                    tensor[index(2)] =
                        leading([tensor[index(0)], tensor[index(1)], tensor[index(2)]]);
                }
            }
        }
        tensor
    }
}

fn procedural_value(kind: u8, row: usize) -> BF {
    if kind == BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS {
        if row < 1 << 16 {
            BF::from_u32_with_reduction(row as u32)
        } else {
            BF::ZERO
        }
    } else if kind == BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW {
        BF::from_u32_with_reduction(((row << 2) & 0xffff) as u32)
    } else {
        panic!("the fixture models only the two procedural kinds it uses")
    }
}

// ── The device run ───────────────────────────────────────────────────────────

fn upload<T: Copy>(context: &ProverContext, host: &[T]) -> DeviceAllocation<T> {
    let mut device: DeviceAllocation<T> = context
        .alloc(host.len().max(1), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device[..host.len()], host, context.get_exec_stream()).unwrap();
    device
}

fn write_symbol(context: &ProverContext, pointer: *mut E4, host: &[E4]) {
    // SAFETY: both symbols this writes are at least `host.len()` E4 long, as
    // pinned by `BWD_SEG_OUTPUT_BANK` and the eq-high slab shape.
    let view = unsafe { DeviceSlice::from_raw_parts_mut(pointer, host.len()) };
    memory_copy_async(view, host, context.get_exec_stream()).unwrap();
}

fn download<T: Copy + Default>(context: &ProverContext, device: &DeviceSlice<T>) -> Vec<T> {
    let mut host = vec![T::default(); device.len()];
    memory_copy_async(&mut host[..], device, context.get_exec_stream()).unwrap();
    host
}

/// One differential run: build the program, run the executor and the tail, and
/// compare both against the host model.
struct Run<'a> {
    context: &'a ProverContext,
    fixture: Fixture,
    atoms: Vec<Atom>,
    program: WindowProgram,
    addressing: WindowAddressing,
    /// Keepalives: the slot bases point into these for the launch's lifetime.
    _base: DeviceAllocation<BF>,
    _ext: DeviceAllocation<E4>,
}

fn build_run<'a>(
    context: &'a ProverContext,
    seed: u64,
    folding_steps: usize,
    atoms: Vec<Atom>,
    base_columns: usize,
    ext_columns: usize,
    shape: WindowShape,
) -> Run<'a> {
    let mut rng = StdRng::seed_from_u64(seed);
    let trace_len = 1usize << folding_steps;

    let base: Vec<BF> = (0..base_columns * trace_len)
        .map(|_| random_bf(&mut rng))
        .collect();
    let ext: Vec<E4> = (0..ext_columns * trace_len)
        .map(|_| random_e4(&mut rng))
        .collect();
    let device_base = upload(context, &base);
    let device_ext = upload(context, &ext);

    let mut bank = vec![E4::ZERO; BWD_SEG_OUTPUT_BANK];
    bank[0] = E4::ONE;
    bank[1] = sub(E4::ZERO, E4::ONE);
    for slot in bank[FIRST_CORE_SLOT..FIRST_CORE_SLOT + 64].iter_mut() {
        *slot = random_e4(&mut rng);
    }
    // A wide linear-E4 atom reads four CONSECUTIVE basis-scaled slots, so every
    // such core owns a quadruple.
    for atom in &atoms {
        if let Atom::LinearExt { core, .. } = atom {
            let value = bank[*core];
            for limb in 0..4 {
                bank[*core + limb] = mul(value, basis(limb));
            }
        }
    }
    write_symbol(context, bwd_seg_coeff_bank_device_ptr(), &bank);
    write_symbol(
        context,
        get_eq_high_constant_device_ptr(),
        &vec![E4::ONE; GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN],
    );

    let claim_point: Vec<E4> = (0..folding_steps + 1)
        .map(|_| random_e4(&mut rng))
        .collect();

    let mut sources = Sources {
        slots: vec![
            BwdSegAddrSlot {
                base: device_base.as_ptr() as *const u8,
                log2_stride: folding_steps as u8,
                origin: BWD_COEFF_ORIGIN_READ_BASE,
                procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
                reserved: [0; 5],
            },
            BwdSegAddrSlot {
                base: device_ext.as_ptr() as *const u8,
                log2_stride: folding_steps as u8,
                origin: BWD_COEFF_ORIGIN_READ_EXT,
                procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
                reserved: [0; 5],
            },
        ],
        lanes: Vec::new(),
        ids: BTreeMap::new(),
    };
    let mut immediates = Vec::new();
    let (words, source_lanes, sections) = encode(&atoms, &mut sources, &mut immediates);
    let mut sections = sections;
    sections[4] = u32::from(shape.bits());

    let program = WindowProgram {
        layer: 0,
        words,
        source_slots: (0..sources.lanes.len() as u16).collect(),
        source_lanes,
        windows: Vec::new(),
        immediates,
        sections,
        coefficient_plans: Vec::new(),
        shape,
        capacities: WindowCapacities::default(),
    };
    let addressing = WindowAddressing {
        slots: sources.slots.clone(),
        lanes: sources.lanes.clone(),
    };

    Run {
        context,
        fixture: Fixture {
            trace_len,
            base,
            ext,
            bank,
            claim_point,
        },
        atoms,
        program,
        addressing,
        _base: device_base,
        _ext: device_ext,
    }
}

impl Run<'_> {
    /// Launch the executor, reduce the partials on the host, and return the
    /// 27-cell tensor plus the resolved entry point's symbol name.
    fn run_executor(&self) -> ([E4; 27], &'static str) {
        let folding_steps = self.fixture.trace_len.trailing_zeros() as usize;
        let stream = self.context.get_exec_stream();
        let mut partials: DeviceAllocation<E4> = self
            .context
            .alloc(
                window_partials_len(self.fixture.trace_len),
                AllocationPlacement::BestFit,
            )
            .unwrap();
        let mut eq_low: DeviceAllocation<E4> = self
            .context
            .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)
            .unwrap();
        let claim_point = upload(self.context, &self.fixture.claim_point);
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            PEELED,
            folding_steps - PEELED,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            self.context,
        )
        .unwrap();

        let binding = build_window_binding(
            &self.program,
            &self.addressing,
            folding_steps,
            WindowRuntimeScratch {
                eq_low: eq_low.as_ptr(),
                partials: partials.as_mut_ptr(),
                partials_capacity: partials.len(),
            },
        )
        .expect("the synthetic program fits every capacity");
        let kernel = resolve_window_kernel(self.program.shape.bits()).expect("a defined shape");
        let row_tiles = window_row_tiles(self.fixture.trace_len);
        // SAFETY: the capacity check inside the binder covers the tensor past
        // the row-tile-major partials.
        let reduced_tensor = unsafe {
            partials
                .as_mut_ptr()
                .add(WINDOW_TAIL_TENSOR_CELLS * row_tiles)
        };
        let launch = WindowLaunch {
            binding,
            kernel,
            row_tiles,
            reduced_tensor,
        };
        super::binding::launch_window_program(&launch, self.context).unwrap();

        let host = download(
            self.context,
            &partials[..WINDOW_TAIL_TENSOR_CELLS * row_tiles],
        );
        stream.synchronize().unwrap();
        let mut tensor = [E4::ZERO; 27];
        for (index, value) in host.iter().enumerate() {
            tensor[index % WINDOW_TAIL_TENSOR_CELLS] =
                add(tensor[index % WINDOW_TAIL_TENSOR_CELLS], *value);
        }
        (tensor, kernel.symbol_name)
    }

    /// The full windowed prologue: executor, then the tail's three round
    /// transitions, against the CPU oracle driven by the model's tensor.
    fn run_tail(&self, arm: WindowTailArm, seed_in: [u32; 8], claim_in: E4, prefactor_in: E4) {
        let folding_steps = self.fixture.trace_len.trailing_zeros() as usize;
        let stream = self.context.get_exec_stream();
        let mut partials: DeviceAllocation<E4> = self
            .context
            .alloc(
                window_partials_len(self.fixture.trace_len),
                AllocationPlacement::BestFit,
            )
            .unwrap();
        let mut eq_low: DeviceAllocation<E4> = self
            .context
            .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)
            .unwrap();
        let claim_point = upload(self.context, &self.fixture.claim_point);
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            PEELED,
            folding_steps - PEELED,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            self.context,
        )
        .unwrap();
        let binding = build_window_binding(
            &self.program,
            &self.addressing,
            folding_steps,
            WindowRuntimeScratch {
                eq_low: eq_low.as_ptr(),
                partials: partials.as_mut_ptr(),
                partials_capacity: partials.len(),
            },
        )
        .expect("the synthetic program fits every capacity");
        let kernel = resolve_window_kernel(self.program.shape.bits()).expect("a defined shape");
        let row_tiles = window_row_tiles(self.fixture.trace_len);
        // SAFETY: as in `run_executor`.
        let reduced_tensor = unsafe {
            partials
                .as_mut_ptr()
                .add(WINDOW_TAIL_TENSOR_CELLS * row_tiles)
        };
        let launch = WindowLaunch {
            binding,
            kernel,
            row_tiles,
            reduced_tensor,
        };
        super::binding::launch_window_program(&launch, self.context).unwrap();

        let mut seed = upload(self.context, &seed_in);
        let mut claim = upload(self.context, &[claim_in]);
        let mut prefactor = upload(self.context, &[prefactor_in]);
        let mut coeffs: DeviceAllocation<E4> = self
            .context
            .alloc(12, AllocationPlacement::BestFit)
            .unwrap();
        let mut challenges: DeviceAllocation<E4> = self
            .context
            .alloc(PEELED, AllocationPlacement::BestFit)
            .unwrap();
        let eq_sizes: GkrEqSizes = make_eq_sizes(folding_steps - PEELED);
        let (slot_base, slot_size) = resolve_active_eq_slot(&eq_sizes, eq_low.as_mut_ptr());
        let state = WindowTailState {
            partials: partials.as_ptr(),
            row_tiles,
            reduced_tensor,
            prev_claim_coords: claim_point.as_ptr(),
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: prefactor.as_mut_ptr(),
            coeffs_out: coeffs.as_mut_ptr(),
            challenges_out: challenges.as_mut_ptr(),
            active_eq_slot_base: slot_base,
            active_eq_size_before_fold: slot_size,
        };
        launch_window_tensor_round_tail(arm, &state, self.context).unwrap();

        let gpu_coeffs = download(self.context, &coeffs[..]);
        let gpu_challenges = download(self.context, &challenges[..]);
        let gpu_seed = download_u32(self.context, &seed[..]);
        let gpu_claim = download(self.context, &claim[..]);
        let gpu_prefactor = download(self.context, &prefactor[..]);
        stream.synchronize().unwrap();

        let mut expected_seed = seed_in;
        let mut expected_claim = claim_in;
        let mut expected_prefactor = prefactor_in;
        let rho: [E4; PEELED] = std::array::from_fn(|index| self.fixture.claim_point[index]);
        let (expected_coeffs, expected_challenges) = tensor_round_tail_reference(
            self.fixture.tensor(&self.atoms),
            &rho,
            &mut expected_seed,
            &mut expected_claim,
            &mut expected_prefactor,
        );
        assert_eq!(
            gpu_coeffs.as_slice(),
            expected_coeffs.as_slice(),
            "{arm:?} coefficients"
        );
        assert_eq!(
            gpu_challenges.as_slice(),
            expected_challenges.as_slice(),
            "{arm:?} challenges"
        );
        assert_eq!(
            gpu_seed.as_slice(),
            expected_seed.as_slice(),
            "{arm:?} seed"
        );
        assert_eq!(gpu_claim[0], expected_claim, "{arm:?} claim");
        assert_eq!(gpu_prefactor[0], expected_prefactor, "{arm:?} eq prefactor");
    }
}

fn download_u32(context: &ProverContext, device: &DeviceSlice<u32>) -> Vec<u32> {
    let mut host = vec![0u32; device.len()];
    memory_copy_async(&mut host[..], device, context.get_exec_stream()).unwrap();
    host
}

// ── The programs the differential drives ─────────────────────────────────────

/// Every section and every opcode class the wire can carry, so the shape mask
/// is the full defined set and the universal entry point runs it.
fn full_program() -> (Vec<Atom>, usize, usize, WindowShape) {
    let mut negative_one = BF::ONE;
    negative_one.negate();
    let banked = BF::from_u32_with_reduction(0x0051_7ade);
    let range16 = Source::Procedural(BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS);
    let low = Source::Procedural(BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW);
    let atoms = vec![
        Atom::Bf {
            core: FIRST_CORE_SLOT,
            term: Term::Linear(Source::Base(0)),
        },
        Atom::Bf {
            core: FIRST_CORE_SLOT + 1,
            term: Term::Product(Source::Base(1), Source::Base(2)),
        },
        Atom::Bf {
            core: FIRST_CORE_SLOT + 2,
            term: Term::Linear(range16),
        },
        Atom::Bf {
            core: FIRST_CORE_SLOT + 3,
            term: Term::Product(Source::Base(3), low),
        },
        Atom::Bf {
            core: FIRST_CORE_SLOT + 4,
            term: Term::Product(range16, low),
        },
        // A deferred-reduction prefix long enough to cross the every-fourth
        // rebase, then a linear tail.
        Atom::BfGroup {
            core: FIRST_CORE_SLOT + 5,
            product_prefix: 5,
            members: vec![
                (BF::ONE, Term::Product(Source::Base(0), Source::Base(1))),
                (
                    negative_one,
                    Term::Product(Source::Base(2), Source::Base(3)),
                ),
                (banked, Term::Product(Source::Base(4), Source::Base(5))),
                (BF::ONE, Term::Product(Source::Base(6), Source::Base(7))),
                (banked, Term::Product(Source::Base(1), Source::Base(4))),
                (negative_one, Term::Linear(Source::Base(5))),
            ],
        },
        // The single-product prefix form.
        Atom::BfGroup {
            core: FIRST_CORE_SLOT + 6,
            product_prefix: 1,
            members: vec![
                (banked, Term::Product(Source::Base(6), low)),
                (BF::ONE, Term::Linear(Source::Base(7))),
            ],
        },
        Atom::LinearExt {
            core: FIRST_CORE_SLOT + 8,
            column: 0,
        },
        Atom::ExtSingleton {
            core: FIRST_CORE_SLOT + 12,
            negate: false,
            term: Term::Product(Source::Base(1), Source::Ext(1)),
        },
        Atom::ExtSingleton {
            core: FIRST_CORE_SLOT + 13,
            negate: true,
            term: Term::Product(Source::Ext(0), Source::Ext(2)),
        },
        Atom::ExtPair {
            core: FIRST_CORE_SLOT + 14,
            members: [
                (false, Term::Product(Source::Base(2), Source::Ext(1))),
                (true, Term::Product(Source::Base(3), Source::Ext(3))),
            ],
        },
        Atom::ExtPair {
            core: FIRST_CORE_SLOT + 15,
            members: [
                (true, Term::Product(Source::Ext(0), Source::Ext(1))),
                (false, Term::Product(Source::Ext(2), Source::Ext(3))),
            ],
        },
    ];
    (atoms, 8, 4, WindowShape::from_bits(0xfff).unwrap())
}

/// A BF-only program that uses no optional feature at all, so ANY well-formed
/// shape mask is a valid superset of it — which is what lets one program drive
/// every ruled entry point.
fn featureless_program() -> (Vec<Atom>, usize, usize) {
    let atoms = vec![
        Atom::Bf {
            core: FIRST_CORE_SLOT,
            term: Term::Linear(Source::Base(0)),
        },
        Atom::Bf {
            core: FIRST_CORE_SLOT + 1,
            term: Term::Product(Source::Base(1), Source::Base(2)),
        },
        Atom::Bf {
            core: FIRST_CORE_SLOT + 2,
            term: Term::Product(Source::Base(0), Source::Base(3)),
        },
    ];
    (atoms, 4, 1)
}

/// The generated entry point compiled for one shape mask, looked up in the
/// registry rather than through the native dispatch map — a compiled mask is not
/// itself always a ruled native row.
fn compiled_symbol(compiled: u16) -> &'static str {
    WINDOWED_R0_KERNELS
        .iter()
        .find(|entry| entry.mask == compiled)
        .unwrap_or_else(|| panic!("no generated kernel for compiled mask {compiled:#05x}"))
        .symbol_name
}

// ── The tests ────────────────────────────────────────────────────────────────

/// Production geometries plus the `folding_steps == 4` minimum: one row tile,
/// several row tiles, and both sides of the eq-group boundary at 11 (the low
/// group holds 8 coordinates, so `folding_steps - 3 = 8` fills it exactly and
/// 9 opens a second group).
const DIFFERENTIAL_GEOMETRIES: [usize; 5] = [4, 9, 11, 12, 14];

#[test]
fn window_differential_full_program_matches_the_host_model() {
    let context = make_test_context(256, 64);
    for (index, folding_steps) in DIFFERENTIAL_GEOMETRIES.into_iter().enumerate() {
        let (atoms, base_columns, ext_columns, shape) = full_program();
        let run = build_run(
            &context,
            0x0057_0001 + index as u64,
            folding_steps,
            atoms,
            base_columns,
            ext_columns,
            shape,
        );
        let (gpu, symbol) = run.run_executor();
        let expected = run.fixture.tensor(&run.atoms);
        assert_eq!(
            gpu, expected,
            "folding_steps {folding_steps} tensor on {symbol}"
        );
    }
}

/// The whole windowed prologue: the executor's tensor driven through both tail
/// arms against the CPU oracle, on the geometry production runs.
#[test]
fn window_differential_tail_matches_the_reference_on_both_arms() {
    let context = make_test_context(256, 64);
    for (index, arm) in [WindowTailArm::Absorbed, WindowTailArm::Split]
        .into_iter()
        .enumerate()
    {
        let (atoms, base_columns, ext_columns, shape) = full_program();
        let run = build_run(
            &context,
            0x0057_0100 + index as u64,
            12,
            atoms,
            base_columns,
            ext_columns,
            shape,
        );
        let mut rng = StdRng::seed_from_u64(0x0057_0200 + index as u64);
        let seed: [u32; 8] = std::array::from_fn(|_| rng.random());
        run.run_tail(arm, seed, random_e4(&mut rng), random_e4(&mut rng));
    }
}

/// Every ruled dispatch row, executed. The featureless program is a valid
/// subset of every mask, so each of the 14 native masks can drive its compiled
/// entry point over the same expected tensor — which makes entry-point coverage
/// observable rather than assumed.
#[test]
fn window_differential_every_ruled_entry_point_executes() {
    let context = make_test_context(256, 64);
    let mut symbols = std::collections::BTreeSet::new();
    let mut masks = std::collections::BTreeSet::new();
    for (index, (native, compiled, _)) in WINDOWED_R0_DISPATCH.iter().enumerate() {
        let (atoms, base_columns, ext_columns) = featureless_program();
        let run = build_run(
            &context,
            0x0057_0300 + index as u64,
            9,
            atoms,
            base_columns,
            ext_columns,
            WindowShape::from_bits(*native).unwrap(),
        );
        let (gpu, symbol) = run.run_executor();
        let expected = run.fixture.tensor(&run.atoms);
        assert_eq!(gpu, expected, "native mask {native:#05x} on {symbol}");
        assert_eq!(
            symbol,
            compiled_symbol(*compiled),
            "native mask {native:#05x} resolved the wrong entry point"
        );
        masks.insert(*native);
        symbols.insert(symbol);
    }
    assert_eq!(masks.len(), 14, "the ruled native masks");
    assert_eq!(symbols.len(), 11, "the compiled entry points");
    assert!(
        symbols.contains(compiled_symbol(WINDOWED_R0_FALLBACK_MASK)),
        "the universal entry point must appear in the ruled image"
    );
}

/// A well-formed mask the ruling does not name falls back to the universal
/// kernel and still evaluates the program correctly.
#[test]
fn window_differential_unruled_mask_runs_on_the_universal_kernel() {
    let context = make_test_context(256, 64);
    let ruled: std::collections::BTreeSet<u16> = WINDOWED_R0_DISPATCH
        .iter()
        .map(|(native, ..)| *native)
        .collect();
    let unruled = (0..=WINDOWED_R0_FALLBACK_MASK)
        .find(|mask| !ruled.contains(mask))
        .expect("the ruling names 14 of 4096 masks");
    let (atoms, base_columns, ext_columns) = featureless_program();
    let run = build_run(
        &context,
        0x0057_0400,
        9,
        atoms,
        base_columns,
        ext_columns,
        WindowShape::from_bits(unruled).unwrap(),
    );
    let (gpu, symbol) = run.run_executor();
    assert_eq!(
        symbol,
        compiled_symbol(WINDOWED_R0_FALLBACK_MASK),
        "unruled mask {unruled:#05x} must fall back"
    );
    assert_eq!(
        gpu,
        run.fixture.tensor(&run.atoms),
        "unruled {unruled:#05x}"
    );
}
