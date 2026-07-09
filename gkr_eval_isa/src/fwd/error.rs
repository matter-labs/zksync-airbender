//! Centralized error types for the forward-eval VM. `From` conversions let the
//! compiler bubble encode/bind failures into `CompileError` cleanly.

use cs::gkr_compiler::dag_ir::RootId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodeError {
    SlotOutOfRange(u8), ColOutOfRange(u16), CellOutOfRange(u16),
    LdcIdxOutOfRange(u16), DescOutOfRange(u16), ArityOutOfRange(usize),
    ExtCellMisaligned(u16),
    /// FMA with `field_lhs=Ext, field_rhs=Base` (EB order) is non-canonical;
    /// the compiler must emit the canonical `BE` form instead.
    NonCanonicalFmaOrder,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    BadOperandType(u16), BadMovDir(u16), NonZeroReserved,
    NonCanonicalField, ZeroArity, Truncated, SpecialIdx(u16),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindError {
    SlotOverflow, ColOverflow(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    NonScratchMaxQuadratic(RootId),
    OutputUnresolved(RootId),
    UncoveredLookupLeaf(u32),     // ExprId.0
    DegenerateRoot(RootId),       // standalone empty Add/Mul root (bare 0/1 output)
    DegenerateConstProduct,       // product of only −1 factors (constant ±1, never real)
    /// v2 acc-domain (§1.2 iff rule): `promote` set on an instruction that does
    /// not require an ext acc, or while the tracked acc domain is already ext.
    PromoteNotRequired,
    /// v2 acc-domain (§1.3): an ext-acc-requiring op (Add{Ext}, Mul{Ext},
    /// Fma{B,E}/{E,E}) executes on a base-domain acc without `promote` set.
    ExtAccWithoutPromote,
    /// v2 acc-domain (§1.4): `Mov DstFromAcc` with field=Base while the tracked
    /// acc domain is ext — no implicit truncation.
    AccTruncation,
    FieldMismatch(String),
    /// v2 (spec §2/§12): a `Global` operand/dst whose instruction field bit
    /// disagrees with its slot's storage field (one slot = one homogeneous
    /// matrix; the field bit must AGREE, it selects nothing).
    FieldStorageMismatch { slot: u8, col: u16 },
    ExtCellMisaligned(u16),
    /// v2 (spec §3): a `Smem` operand/dst whose field bit disagrees with the PLACED
    /// width of the value occupying that cell/bucket at that instruction. `cell` is
    /// the WIRE index (bucket index for an Ext field bit, bf-lane index for Base).
    SmemRegionMismatch { cell: u16 },
    BudgetBelowFloor { floor: usize, budget: usize },
    /// `validate_circuit_schedule` (or `load_committed_schedule` I/O/parse) failed;
    /// the wrapped message is the validator's/serde's own diagnostic.
    InvalidSchedule(String),
    Bind(BindError),
    Encode(EncodeError),
}
impl From<BindError> for CompileError { fn from(e: BindError) -> Self { CompileError::Bind(e) } }
impl From<EncodeError> for CompileError { fn from(e: EncodeError) -> Self { CompileError::Encode(e) } }

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterpError {
    UnknownSlot(u8), UnknownSpecial(u16), UnknownChallenge(u16),
    UnknownConst(u16), MalformedInstr(String),
    Peek(crate::fwd::peek::PeekError),
}
