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
    BadOperandType(u16), BadMovDir(u16), NonZeroReserved, PromoteSet,
    NonCanonicalField, NonCanonicalSign, ZeroArity, Truncated, SpecialIdx(u16),
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
    PromoteRejected,
    FieldMismatch(String),
    ExtCellMisaligned(u16),
    BudgetBelowFloor { floor: usize, budget: usize },
    Bind(BindError),
    Encode(EncodeError),
}
impl From<BindError> for CompileError { fn from(e: BindError) -> Self { CompileError::Bind(e) } }
impl From<EncodeError> for CompileError { fn from(e: EncodeError) -> Self { CompileError::Encode(e) } }

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterpError {
    UnknownSlot(u8), UnknownSpecial(u16), UnknownChallenge(u16),
    UnknownConst(u16), MalformedInstr(String),
}
