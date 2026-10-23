import Airbender.Review.Trace.UnifiedReduced.Paths.SpanProjection

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- Exact finite RAM protection for the native algorithms: G state16/message16,
    extended BLAKE state24/message16, Keccak physical31 two-word lanes. -/
def path_span_protected_addresses (span : Delegation.Caller.HashSpan)
    (pointers : BitVec 5 → BitVec 32) : List (BitVec 32) :=
  match span with
  | .blakeG _ =>
    (List.range 16).map (fun i => pointers 10 + BitVec.ofNat 32 (4 * i)) ++
      (List.range 16).map (fun i => pointers 11 + BitVec.ofNat 32 (4 * i))
  | .blakeRound _ =>
    (List.range 24).map (fun i => pointers 10 + BitVec.ofNat 32 (4 * i)) ++
      (List.range 16).map (fun i => pointers 11 + BitVec.ofNat 32 (4 * i))
  | .keccak => (List.range 62).map (fun i => pointers 11 + BitVec.ofNat 32 (4 * i))

/-- Pointer GPR frames across ordinary gaps. Actual RAM writes are unrestricted
    here and must separately satisfy the protected-address certificate. -/
structure PathSpanPointerGaps [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program) : Prop where
  code : ∀ cut, span.start (PathCompleteSpan.first span.span) + 8 ≤ cut →
    cut ≤ span.start (PathCompleteSpan.last span.span) → cut % 4 = 0 →
    (¬ ∃ i : Fin span.span.callCount, cut = span.start i + 4) →
    ∃ instruction : SailRV32.instruction, PathInstructionPreparation data program cut instruction ∧
      ∀ register ∈ path_span_pointer_registers span.span, PathRegisterFrame register instruction

/-- An ordinary gap either preserves RAM by syntax, or stores at an address
    computed from original code/dataflow and statically outside the finite
    protected set. The stored value is unrestricted. -/
inductive PathRamProtectedInstruction [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat)
    (protectedAddresses : List (BitVec 32)) : SailRV32.instruction → Prop where
  | readOnly {instruction : SailRV32.instruction}
      (form : PathRamReadOnlyInstruction instruction) :
      PathRamProtectedInstruction data program cut protectedAddresses instruction
  | store (immediate : BitVec 12) (stored source : BitVec 5) (baseValue : BitVec 32)
      (nonzero : source ≠ 0)
      (flow : PathControllerDataflow data program (cut - 4) source baseValue)
      (disjoint : baseValue + SailRV32.Functions.sign_extend (m := 32) immediate ∉ protectedAddresses) :
      PathRamProtectedInstruction data program cut protectedAddresses
        (.STORE (immediate, .Regidx stored, .Regidx source, 4))

/-- Public computed pointers and effective store addresses. This complements
    the unchanged arbitrary-pointer readonly variant. Native pointer/source
    reads and protected refresh frames are conclusions of accepted matching. -/
structure PathSpanComputedStoreGaps [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program) where
  pointerValues : BitVec 5 → BitVec 32
  pointerPreparation : ∀ register ∈ path_span_pointer_registers span.span,
    PathControllerDataflow data program (span.start (PathCompleteSpan.first span.span)) register
      (pointerValues register)
  code : ∀ cut, span.start (PathCompleteSpan.first span.span) + 8 ≤ cut →
    cut ≤ span.start (PathCompleteSpan.last span.span) → cut % 4 = 0 →
    (¬ ∃ i : Fin span.span.callCount, cut = span.start i + 4) →
    ∃ instruction : SailRV32.instruction, PathInstructionPreparation data program cut instruction ∧
      (∀ register ∈ path_span_pointer_registers span.span, PathRegisterFrame register instruction) ∧
      PathRamProtectedInstruction data program cut
        (path_span_protected_addresses span.span pointerValues) instruction

end Airbender.UnifiedReduced.Caller
