//! The SEGMENTED lean VM's by-value launch descriptors (segmented-lean-VM
//! design §3, §5, §7).
//!
//! THIS FILE IS ONE HALF OF AN ABI. Its CUDA half is
//! `native/prover/gkr/backward/segmented_vm.cuh`, which Task 7 creates carrying
//! the same field offsets under `static_assert`. Neither half may move without
//! the other in the same commit. The three drift directions and what closes each
//! are exactly as documented in [`desc`](super::desc): Rust-side drift is a build
//! failure (the `const _: () = assert!(...)` blocks below), CUDA-side STRUCT
//! drift is a build failure under nvcc, and CUDA-side CONSTANT drift is caught
//! only by the header-text matchers — which do not exist until Task 7 writes the
//! header, so until then [`seg_abi_tests`](super::seg_abi_tests) is the whole
//! gate.
//!
//! # What this lineage does NOT carry
//!
//! It is a separate descriptor, not a variant of [`desc::BwdCoeffDesc`], and the
//! absences are load-bearing:
//!
//!   * **No challenge pointer.** Fold challenges have exactly ONE authority, the
//!     `ab_gkr_main_layer_claim_point` `__constant__` symbol (the incumbent
//!     route), so `round_challenges` / `n_round_challenges` are gone.
//!   * **No `cell_budget`.** There is no cell file and no residency genome: the
//!     prologue folds sources into registers, the eval loop reads them.
//!   * **No `num_words`.** [`BwdSegDesc::list_offset`] carries the program
//!     length: `list_offset[k]` IS the end of the stream.
//!   * **No coefficient recipe index on the seed path** — see
//!     [`BwdSegDesc::c_init`].
//!
//! What it DOES share with the cell-era descriptor is deliberate and minimal:
//! [`desc::BwdCoeffSourceWindow`] (imported, never forked — including
//! `procedural_kind` at offset 28) and [`desc::BWD_COEFF_PUBLISH_TARGET_DEPTH`]
//! (imported, never duplicated). Everything else — the coefficient bank
//! included — this lineage owns, which is what keeps Task 11's retirement of the
//! cell-era lineage a deletion rather than a rehoming.
//!
//! # The program stream
//!
//! `program` is the LEAN wire (`gkr_eval_isa::bwd::coeff::lean`): one fixed
//! 8-byte header-first record per term, `[class:3 @13 | coeff_idx:13 @0]` then
//! two source slots and a reserved word. It is embedded BY VALUE in the
//! `__grid_constant__` parameter; [`BwdSegProgPtrDesc`] is the spike-only A/B
//! twin that reads it from device memory instead (§5).

use core::mem::{align_of, size_of};

use gkr_eval_isa::bwd::coeff::lean::SOURCE_NONE;
use gkr_eval_isa::bwd::coeff::limits::{
    in_scope, DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES,
    LEAN_DESCRIPTOR_PROGRAM_BYTES, LEAN_DESCRIPTOR_PROGRAM_WORDS, MAX_COEFFICIENT_ENCODINGS,
    SOURCE_WINDOW_COLUMNS,
};
use gkr_eval_isa::bwd::coeff::model::CoefficientRecipeId;
use gkr_eval_isa::bwd::coeff::schedule::PUBLISH_TARGET_DEPTH;

use super::desc::{BwdCoeffSourceWindow, BWD_COEFF_PUBLISH_TARGET_DEPTH};
use crate::primitives::field::E4;
use crate::primitives::utils::WARP_SIZE;
use crate::prover::gkr::backward::GkrEqSizes;

// ── Capacities and launch geometry ───────────────────────────────────────────

/// The by-value kernel-argument cap. `size_of::<BwdSegDesc>() <=
/// BWD_SEG_DESC_CAP` is the FINAL authority on the descriptor's shape.
pub(crate) const BWD_SEG_DESC_CAP: usize = 32_764;
/// Descriptor alignment. Load-bearing rather than cosmetic: it is what places
/// [`BwdSegDesc::program`] — the descriptor's FIRST field — on a 16-byte
/// boundary, which is the only reason the lean census's one-word round-up to
/// [`LEAN_DESCRIPTOR_PROGRAM_WORDS`] buys anything.
pub(crate) const BWD_SEG_DESC_ALIGN: usize = 16;

/// Warps a block may run, i.e. the largest legal `K` of the round-robin term
/// split. One warp per term list, `blockDim = 32 * k`, so `K` tops out exactly
/// where the CUDA block does.
pub(crate) const BWD_SEG_MAX_K: usize = 32;
/// The CUDA hardware maximum block size, which is what caps [`BWD_SEG_MAX_K`].
pub(crate) const BWD_SEG_MAX_THREADS_PER_BLOCK: usize = 1_024;

/// Slots in this lineage's OWN `__constant__` coefficient bank
/// (`ab_gkr_bwd_seg_coeff_bank`, declared on the CUDA side in Task 7). No
/// `backward::flat` symbol is involved.
///
/// **RR ruling 2026-07-27: the two reserved literal ids are MATERIALIZED at the
/// bank head** — `bank[0] = ONE`, `bank[1] = NEG_ONE`, banked recipes from index
/// [`CoefficientRecipeId::RESERVED`] on — so the kernel resolves every
/// coefficient with ONE uniform `bank[coeff_idx]` load: no ±ONE fast path, no
/// branch, no offset subtraction. The census is why: 149 of 15,860 terms carry
/// `+1` and none carries `−1`, so a per-term branch to save 0.94% of the e4
/// multiplies is a net loss. Host lowering (Task 6) owns the materialization;
/// wire coefficient ids are reserved-INCLUSIVE and the kernel indexes raw.
///
/// Sized from the census (`1,138` recipes `+ 2` literals `= 1,140`), rounded up
/// so the bank is exactly 18 KiB of the 64 KB per-module `__constant__` budget —
/// 12 slots of slack, which [`seg_abi_tests`](super::seg_abi_tests) prints.
pub(crate) const BWD_SEG_CONST_BANK: usize = 1_152;

/// Source-table slots the descriptor can hold: the census maximum of 1,062
/// rounded up to a multiple of 16 slots, which makes both source-indexed arrays
/// ([`BwdSegDesc::fold_source`] and [`BwdSegDesc::source`]) a whole number of
/// 16-byte lines.
pub(crate) const BWD_SEG_MAX_SOURCES: usize = 1_072;

const _: () = {
    assert!(BWD_SEG_DESC_CAP == KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(BWD_SEG_DESC_ALIGN == DESCRIPTOR_ALIGNMENT_BYTES);

    // One warp per list, and the block is the cap.
    assert!(BWD_SEG_MAX_K * WARP_SIZE as usize == BWD_SEG_MAX_THREADS_PER_BLOCK);
    assert!(BWD_SEG_MAX_THREADS_PER_BLOCK == 1_024);
    // `k` and every `list_offset` entry are u16.
    assert!(BWD_SEG_MAX_K <= u16::MAX as usize);
    assert!(LEAN_DESCRIPTOR_PROGRAM_WORDS <= u16::MAX as usize);
    assert!(LEAN_DESCRIPTOR_PROGRAM_BYTES == LEAN_DESCRIPTOR_PROGRAM_WORDS * size_of::<u16>());
    // `term_count` is a u16 as well.
    assert!(in_scope::MAX_TERMS <= u16::MAX as usize);

    // The bank covers every reserved-inclusive coefficient id the corpus can
    // name, stays inside the thirteen coefficient bits that name it, and fits the
    // per-module constant budget.
    assert!(BWD_SEG_CONST_BANK >= in_scope::MAX_COEFFICIENT_RECIPES + 2);
    assert!(
        in_scope::MAX_COEFFICIENT_RECIPES + 2
            == in_scope::MAX_COEFFICIENT_RECIPES + CoefficientRecipeId::RESERVED as usize
    );
    assert!(BWD_SEG_CONST_BANK <= MAX_COEFFICIENT_ENCODINGS);
    assert!(BWD_SEG_CONST_BANK * size_of::<E4>() == 18 * 1_024);
    assert!(BWD_SEG_CONST_BANK * size_of::<E4>() <= 64 * 1_024);

    // The source capacity is the MEASUREMENT rounded up by strictly less than one
    // 16-slot quantum, so it cannot silently drift into headroom.
    assert!(BWD_SEG_MAX_SOURCES >= in_scope::MAX_SOURCES);
    assert!(BWD_SEG_MAX_SOURCES - in_scope::MAX_SOURCES < 16);
    assert!(BWD_SEG_MAX_SOURCES % 16 == 0);
    // A slot index rides the lean wire as a u16 whose 0xFFFF is the "no second
    // source" sentinel, so the capacity must stay strictly below it.
    assert!(BWD_SEG_MAX_SOURCES < SOURCE_NONE as usize);

    // The window struct is imported, not forked, so its publication policy comes
    // along verbatim: publish on first physical access iff
    // `target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH`. Tied to `gkr_eval_isa`
    // here as well as in `desc.rs`, so Task 11's deletion of the cell-era lineage
    // cannot quietly change the threshold this lineage was measured under.
    assert!(BWD_COEFF_PUBLISH_TARGET_DEPTH == PUBLISH_TARGET_DEPTH);
};

// ── Source table ─────────────────────────────────────────────────────────────

/// One entry of the per-launch source table: where a source is read from, and
/// how this round resolves it.
///
/// `class` is the per-`(source, round)` SOURCE class assigned by Task 6's round
/// lowering — `BfDirect = 0`, `BfInlineD1 = 1`, `BfInlineD2 = 2`, `E4Direct = 3`,
/// `ProceduralInline = 4` — and is NOT the lean wire's three-bit TERM class
/// (`gkr_eval_isa::bwd::coeff::lean::LEAN_CLASS_SHIFT`). The two are independent
/// axes: the term class fixes the projection and arity of an operation, the
/// source class fixes how the operand behind a slot is produced. The enum with
/// those discriminants is Task 6's, so it is the authority; this field is the
/// byte it travels in.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[allow(dead_code)] // TASK 6 fills these; TASK 7 reads them on the device.
pub(crate) struct BwdSegSourceRecord {
    /// Slot in [`BwdSegDesc::window`].
    pub window: u8,
    /// This round's source class (see the struct doc).
    pub class: u8,
    /// Column WITHIN the window: the address is
    /// `window.read_base + column * window.read_stride_bytes`.
    pub column: u16,
}

const _: () = {
    use core::mem::offset_of;

    assert!(size_of::<BwdSegSourceRecord>() == 4);
    assert!(align_of::<BwdSegSourceRecord>() == 2);
    assert!(offset_of!(BwdSegSourceRecord, window) == 0);
    assert!(offset_of!(BwdSegSourceRecord, class) == 1);
    assert!(offset_of!(BwdSegSourceRecord, column) == 2);
    // The window slot is a byte, and a column is window-relative.
    assert!(in_scope::MAX_SOURCE_WINDOWS_USED <= u8::MAX as usize);
    assert!(SOURCE_WINDOW_COLUMNS <= u16::MAX as usize + 1);
};

// ── The inline-program descriptor ────────────────────────────────────────────

/// The complete by-value launch descriptor, passed as a single
/// `__grid_constant__` kernel parameter (§3).
///
/// Field order is chosen so `program` sits at offset 0 — 16-byte aligned by the
/// descriptor's own alignment, at no cost in padding — and so the launch tail's
/// pointers land naturally aligned after the arrays.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
#[allow(dead_code)] // TASK 6 fills this; TASK 7 launches with it.
pub(crate) struct BwdSegDesc {
    /// The lean term stream, embedded by value. Warp `w` walks
    /// `program[list_offset[w]..list_offset[w + 1]]`.
    pub program: [u16; LEAN_DESCRIPTOR_PROGRAM_WORDS],
    /// `k + 1` word offsets into [`Self::program`]: entry `w` is warp `w`'s
    /// first word and `list_offset[k]` is the END of the stream. This is why the
    /// descriptor needs no separate program-length field.
    pub list_offset: [u16; BWD_SEG_MAX_K + 1],
    /// Term lists, i.e. warps in the block. `blockDim == 32 * k`.
    pub k: u16,
    /// Terms across all `k` lists, so
    /// `list_offset[k] == LEAN_WORDS_PER_TERM * term_count`.
    pub term_count: u16,
    /// Live entries of [`Self::source`].
    pub num_sources: u16,
    /// Leading entries of [`Self::fold_source`] the prologue folds.
    pub num_foldable: u16,
    /// Source slots the JAOT prologue folds, in FOLD order: warp `w` takes
    /// `s = w, w + k, w + 2k, …`. The order is a performance contract (§7) — the
    /// sources the eval loop touches EARLIEST are folded LAST, so they are the
    /// warmest in L1 when eval starts.
    pub fold_source: [u16; BWD_SEG_MAX_SOURCES],
    /// The per-launch source table. Entries at and past [`Self::num_sources`]
    /// are zero-filled and never read.
    pub source: [BwdSegSourceRecord; BWD_SEG_MAX_SOURCES],
    /// Live source windows, IMPORTED from the cell-era descriptor rather than
    /// forked (`procedural_kind` at offset 28 included), so both lineages share
    /// one window layout and one publication policy
    /// ([`BWD_COEFF_PUBLISH_TARGET_DEPTH`]).
    pub window: [BwdCoeffSourceWindow; in_scope::MAX_SOURCE_WINDOWS_USED],
    /// The per-thread `acc_c0` seed as RESOLVED E4 limbs, all-zero when the
    /// layer has none.
    ///
    /// A deliberate divergence from the cell-era `c_init: u16`, which was a
    /// coefficient RECIPE INDEX the kernel had to resolve through the bank: with
    /// limbs the seed path needs no bank lookup at all, and a reserved-literal id
    /// resolves host-side exactly like a banked one. Zero is also a safe
    /// "absent" value here — an additive identity, not a sentinel that could
    /// alias a live index — so no `*_NONE` constant is needed.
    pub c_init: [u32; 4],
    /// Evaluated E4 coefficients for the `ptr` loader specialization. The
    /// `const` loader reads this lineage's `__constant__` bank and ignores it.
    /// Reserved-inclusive either way: `[ONE, NEG_ONE, recipes…]`.
    pub coefficients: *const E4,
    /// Production factored-eq low table; high tables remain in `ab_gkr_eq_high`.
    pub eq_low: *const E4,
    /// `2 * logical_rows` entries: `eq * acc_c0` in `[0, logical_rows)` and
    /// `eq * acc_c2` in `[logical_rows, 2 * logical_rows)`.
    pub contributions: *mut E4,
    pub eq_sizes: GkrEqSizes,
    /// Bank entries, reserved literals included.
    pub n_coefficients: u32,
    /// Rows this launch evaluates. Also the contribution half-stride: the
    /// incumbent `acc_size`.
    pub logical_rows: u32,
    /// Explicit: makes the SIZE a multiple of [`BWD_SEG_DESC_ALIGN`] without
    /// implicit trailing padding the two languages would have to agree on.
    /// Never read by the kernel.
    pub pad: [u32; 1],
}

impl BwdSegDesc {
    /// An empty descriptor: null pointers, no windows, no program.
    ///
    /// `[u16; LEAN_DESCRIPTOR_PROGRAM_WORDS]` is far past the arity `Default` is
    /// derived for, so this is written out rather than derived.
    #[allow(dead_code)] // TASK 6 builds descriptors from this.
    pub(crate) fn empty() -> Self {
        Self {
            program: [0; LEAN_DESCRIPTOR_PROGRAM_WORDS],
            list_offset: [0; BWD_SEG_MAX_K + 1],
            k: 0,
            term_count: 0,
            num_sources: 0,
            num_foldable: 0,
            fold_source: [0; BWD_SEG_MAX_SOURCES],
            source: [BwdSegSourceRecord::default(); BWD_SEG_MAX_SOURCES],
            window: [BwdCoeffSourceWindow::default(); in_scope::MAX_SOURCE_WINDOWS_USED],
            c_init: [0; 4],
            coefficients: std::ptr::null(),
            eq_low: std::ptr::null(),
            contributions: std::ptr::null_mut(),
            eq_sizes: GkrEqSizes::zeroed(),
            n_coefficients: 0,
            logical_rows: 0,
            pad: [0; 1],
        }
    }
}

// ── The device-program A/B twin (§5) ─────────────────────────────────────────

/// [`BwdSegDesc`] field-for-field, with the inline `program` array REPLACED by a
/// device pointer and its length.
///
/// Dropping the array is the whole point: keeping it and merely not reading it
/// would leave 14,336 bytes resident in every launch's parameter space and
/// measure nothing. Inline fit proves the ABI is feasible, not that `K` warps
/// streaming a 14 KiB param-space program alongside an 18 KiB `__constant__`
/// coefficient bank wins on constant-cache behaviour — this twin is the one
/// comparison point that answers it.
///
/// Lowering leaves `program` NULL; the harness uploads
/// `BwdSegSetup::program_words` to a device buffer and patches the pointer into
/// its host copy of the descriptor before launch — the descriptor is a by-value
/// kernel parameter, so patching the host copy IS the mechanism. Ownership of
/// the staging buffer is the caller's, exactly as for the coefficient bank.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
#[allow(dead_code)] // TASK 6 fills this; TASK 7 launches the progptr family.
pub(crate) struct BwdSegProgPtrDesc {
    /// Device-resident lean term stream, `program_words` u16 words long.
    pub program: *const u16,
    pub program_words: u32,
    /// See [`BwdSegDesc::list_offset`]; offsets index the DEVICE stream here.
    pub list_offset: [u16; BWD_SEG_MAX_K + 1],
    pub k: u16,
    pub term_count: u16,
    pub num_sources: u16,
    pub num_foldable: u16,
    pub fold_source: [u16; BWD_SEG_MAX_SOURCES],
    pub source: [BwdSegSourceRecord; BWD_SEG_MAX_SOURCES],
    pub window: [BwdCoeffSourceWindow; in_scope::MAX_SOURCE_WINDOWS_USED],
    pub c_init: [u32; 4],
    pub coefficients: *const E4,
    pub eq_low: *const E4,
    pub contributions: *mut E4,
    pub eq_sizes: GkrEqSizes,
    pub n_coefficients: u32,
    pub logical_rows: u32,
    /// See [`BwdSegDesc::pad`]. Three words rather than one: the head is 12
    /// bytes here instead of 14,336, so the tail lands elsewhere modulo 16.
    pub pad: [u32; 3],
}

impl BwdSegProgPtrDesc {
    /// An empty descriptor; see [`BwdSegDesc::empty`].
    #[allow(dead_code)] // TASK 6 builds descriptors from this.
    pub(crate) fn empty() -> Self {
        Self {
            program: std::ptr::null(),
            program_words: 0,
            list_offset: [0; BWD_SEG_MAX_K + 1],
            k: 0,
            term_count: 0,
            num_sources: 0,
            num_foldable: 0,
            fold_source: [0; BWD_SEG_MAX_SOURCES],
            source: [BwdSegSourceRecord::default(); BWD_SEG_MAX_SOURCES],
            window: [BwdCoeffSourceWindow::default(); in_scope::MAX_SOURCE_WINDOWS_USED],
            c_init: [0; 4],
            coefficients: std::ptr::null(),
            eq_low: std::ptr::null(),
            contributions: std::ptr::null_mut(),
            eq_sizes: GkrEqSizes::zeroed(),
            n_coefficients: 0,
            logical_rows: 0,
            pad: [0; 3],
        }
    }
}

// ── Kernel-argument budget ───────────────────────────────────────────────────

/// Param-space bytes a formal list occupies under the C parameter-packing rules
/// both nvcc and this side follow: each formal starts at the next multiple of its
/// own alignment.
///
/// `formals` is `(size, align)` in DECLARATION order.
#[allow(dead_code)] // TASK 7 owns the signatures these budgets describe.
const fn kernel_argument_bytes(formals: &[(usize, usize)]) -> usize {
    let mut total: usize = 0;
    let mut index = 0;
    while index < formals.len() {
        let (size, align) = formals[index];
        total = total.next_multiple_of(align) + size;
        index += 1;
    }
    total
}

/// Total kernel-argument bytes one launch of the inline-program family consumes.
///
/// The ASSUMED formal-parameter list is `(BwdSegDesc desc)` and nothing else —
/// everything else a launch needs is out of band: fold challenges in the
/// `ab_gkr_main_layer_claim_point` `__constant__` symbol, the coefficient bank in
/// this lineage's own `__constant__` symbol (or, under the `ptr` loader, behind
/// [`BwdSegDesc::coefficients`]), the epilogue plane in DYNAMIC shared memory,
/// and `k` in [`BwdSegDesc::k`]. If Task 7's signature grows a formal, add it
/// here and update the pin in [`seg_abi_tests`](super::seg_abi_tests) in the same
/// commit.
#[allow(dead_code)] // TASK 7 launches with it.
pub(crate) const BWD_SEG_INLINE_KERNEL_ARGUMENT_BYTES: usize =
    kernel_argument_bytes(&[(size_of::<BwdSegDesc>(), align_of::<BwdSegDesc>())]);

/// Total kernel-argument bytes one launch of the progptr family consumes; the
/// assumed formal list is `(BwdSegProgPtrDesc desc)`. See
/// [`BWD_SEG_INLINE_KERNEL_ARGUMENT_BYTES`].
#[allow(dead_code)] // TASK 7 launches with it.
pub(crate) const BWD_SEG_PROGPTR_KERNEL_ARGUMENT_BYTES: usize = kernel_argument_bytes(&[(
    size_of::<BwdSegProgPtrDesc>(),
    align_of::<BwdSegProgPtrDesc>(),
)]);

// The layout, pinned against the same literals `segmented_vm.cuh` will
// `static_assert`. A change to either struct fails one of the two builds.
const _: () = {
    use core::mem::offset_of;

    assert!(size_of::<BwdSegDesc>() == 21_456);
    assert!(align_of::<BwdSegDesc>() == BWD_SEG_DESC_ALIGN);
    // The FINAL authority on the descriptor's shape.
    assert!(size_of::<BwdSegDesc>() <= BWD_SEG_DESC_CAP);
    assert!(offset_of!(BwdSegDesc, program) == 0);
    assert!(offset_of!(BwdSegDesc, list_offset) == 14_336);
    assert!(offset_of!(BwdSegDesc, k) == 14_402);
    assert!(offset_of!(BwdSegDesc, term_count) == 14_404);
    assert!(offset_of!(BwdSegDesc, num_sources) == 14_406);
    assert!(offset_of!(BwdSegDesc, num_foldable) == 14_408);
    assert!(offset_of!(BwdSegDesc, fold_source) == 14_410);
    assert!(offset_of!(BwdSegDesc, source) == 16_554);
    // Six bytes of implicit padding precede `window`: the source array is
    // 2-byte-aligned and the window array is 8-byte-aligned. nvcc inserts the
    // same gap by the same rule, and the offsets on both sides are asserted, so
    // it needs no explicit field.
    assert!(offset_of!(BwdSegDesc, window) == 20_848);
    assert!(offset_of!(BwdSegDesc, c_init) == 21_392);
    assert!(offset_of!(BwdSegDesc, coefficients) == 21_408);
    assert!(offset_of!(BwdSegDesc, eq_low) == 21_416);
    assert!(offset_of!(BwdSegDesc, contributions) == 21_424);
    assert!(offset_of!(BwdSegDesc, eq_sizes) == 21_432);
    assert!(offset_of!(BwdSegDesc, n_coefficients) == 21_444);
    assert!(offset_of!(BwdSegDesc, logical_rows) == 21_448);
    assert!(offset_of!(BwdSegDesc, pad) == 21_452);
    // The program stream starts on a 16-byte boundary and can be buffered
    // through wide loads.
    assert!(offset_of!(BwdSegDesc, program) % BWD_SEG_DESC_ALIGN == 0);
    // `pad` is the tail, and it is what makes the size a whole number of
    // alignment quanta.
    assert!(offset_of!(BwdSegDesc, pad) + size_of::<[u32; 1]>() == size_of::<BwdSegDesc>());
    assert!(size_of::<BwdSegDesc>() % BWD_SEG_DESC_ALIGN == 0);

    assert!(size_of::<BwdSegProgPtrDesc>() == 7_136);
    assert!(align_of::<BwdSegProgPtrDesc>() == BWD_SEG_DESC_ALIGN);
    assert!(size_of::<BwdSegProgPtrDesc>() <= BWD_SEG_DESC_CAP);
    assert!(offset_of!(BwdSegProgPtrDesc, program) == 0);
    assert!(offset_of!(BwdSegProgPtrDesc, program_words) == 8);
    assert!(offset_of!(BwdSegProgPtrDesc, list_offset) == 12);
    assert!(offset_of!(BwdSegProgPtrDesc, k) == 78);
    assert!(offset_of!(BwdSegProgPtrDesc, term_count) == 80);
    assert!(offset_of!(BwdSegProgPtrDesc, num_sources) == 82);
    assert!(offset_of!(BwdSegProgPtrDesc, num_foldable) == 84);
    assert!(offset_of!(BwdSegProgPtrDesc, fold_source) == 86);
    assert!(offset_of!(BwdSegProgPtrDesc, source) == 2_230);
    assert!(offset_of!(BwdSegProgPtrDesc, window) == 6_520);
    assert!(offset_of!(BwdSegProgPtrDesc, c_init) == 7_064);
    assert!(offset_of!(BwdSegProgPtrDesc, coefficients) == 7_080);
    assert!(offset_of!(BwdSegProgPtrDesc, eq_low) == 7_088);
    assert!(offset_of!(BwdSegProgPtrDesc, contributions) == 7_096);
    assert!(offset_of!(BwdSegProgPtrDesc, eq_sizes) == 7_104);
    assert!(offset_of!(BwdSegProgPtrDesc, n_coefficients) == 7_116);
    assert!(offset_of!(BwdSegProgPtrDesc, logical_rows) == 7_120);
    assert!(offset_of!(BwdSegProgPtrDesc, pad) == 7_124);
    assert!(
        offset_of!(BwdSegProgPtrDesc, pad) + size_of::<[u32; 3]>()
            == size_of::<BwdSegProgPtrDesc>()
    );
    assert!(size_of::<BwdSegProgPtrDesc>() % BWD_SEG_DESC_ALIGN == 0);
    // The A/B twin really drops the array rather than leaving it resident.
    assert!(
        size_of::<BwdSegDesc>() - size_of::<BwdSegProgPtrDesc>()
            >= LEAN_DESCRIPTOR_PROGRAM_BYTES - BWD_SEG_DESC_ALIGN
    );
};
