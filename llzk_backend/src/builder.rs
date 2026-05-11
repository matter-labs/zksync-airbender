//! Builder types for encapsulating common codegen tasks.
//!
//! Contains:
//! - A module-scoped helper with stateless factory methods.
//! - An operations builder meant for creating ops inside a function.
//! - A struct builder.

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::ops::Deref;

use anyhow::anyhow;
use anyhow::Result;
use llzk::builder::OpBuilder;
use llzk::dialect::array::ArrayCtor;
use llzk::dialect::bool;
use llzk::dialect::constrain;
use llzk::dialect::felt;
use llzk::operation::WalkOperationMutLike;
use llzk::prelude::dialect::array;
use llzk::prelude::dialect::r#struct;
use llzk::prelude::melior_dialects::arith;
use llzk::prelude::*;
use llzk::utils::IsA;
use melior::ir::operation::OperationMutLike;
use melior::ir::Identifier;
use prover::cs::definitions::REGISTER_SIZE;

use crate::codegen::SpecialCsrPropertiesMetadata;
use crate::config::DebugLocationStyle;
use crate::field::FieldInfo;

/// Synthetic semantic debug location used to annotate emitted LLZK IR even when the source
/// circuit does not carry real file spans.
///
/// The filename identifies the lowering subsystem, while the line/column pair encodes stable
/// zero-based indices inside that subsystem. For some location families, the filename also carries
/// a descriptive hook kind (for example `llzk://compute/runtime/oracle_u32`). These locations are
/// meant for analyzer correlation, not source navigation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticLocation {
    path: Cow<'static, str>,
    line: usize,
    column: usize,
}

impl SemanticLocation {
    /// Create a semantic location from its virtual path and zero-based line/column coordinates.
    pub const fn new(path: &'static str, line: usize, column: usize) -> Self {
        Self {
            path: Cow::Borrowed(path),
            line,
            column,
        }
    }

    /// Create a semantic location whose virtual path is derived dynamically.
    pub fn new_owned(path: String, line: usize, column: usize) -> Self {
        Self {
            path: Cow::Owned(path),
            line,
            column,
        }
    }

    /// Location family for boolean constraints synthesized from declared boolean variables.
    pub fn constrain_boolean(index: usize) -> Self {
        Self::new("llzk://constrain/booleans", index, 0)
    }

    /// Location family for explicit range checks.
    pub fn constrain_range_check(index: usize) -> Self {
        Self::new("llzk://constrain/range_checks", index, 0)
    }

    /// Location family for top-level lookup constraints.
    pub fn constrain_lookup(index: usize) -> Self {
        Self::new("llzk://constrain/lookups", index, 0)
    }

    /// Location family for top-level algebraic constraints.
    pub fn constrain_constraint(index: usize) -> Self {
        Self::new("llzk://constrain/constraints", index, 0)
    }

    /// Location family for Picus extraction metadata parallel constraints.
    pub fn constrain_parallel_constraint(index: usize) -> Self {
        Self::new("llzk://constrain/parallel_constraints", index, 0)
    }

    /// Location family for compiled degree-1 constraints.
    pub fn constrain_compiled_degree1(index: usize) -> Self {
        Self::new("llzk://constrain/compiled/degree1", index, 0)
    }

    /// Location family for compiled degree-2 constraints.
    pub fn constrain_compiled_degree2(index: usize) -> Self {
        Self::new("llzk://constrain/compiled/degree2", index, 0)
    }

    /// Location family for equalities bridging logical LLZK members back to compiled columns.
    pub fn constrain_compiled_member_bridge(index: usize) -> Self {
        Self::new("llzk://constrain/compiled/member_bridge", index, 0)
    }

    /// Location family for equalities bridging explicit LLZK input args to compiled columns.
    pub fn constrain_compiled_input_bridge(index: usize) -> Self {
        Self::new("llzk://constrain/compiled/input_bridge", index, 0)
    }

    /// Location family for compiler-added variable linkage equalities.
    pub fn constrain_linked_variable(index: usize) -> Self {
        Self::new("llzk://constrain/linked_variables", index, 0)
    }

    /// Location family for compiler-derived executor timestamp constraints.
    pub fn constrain_executor_timestamp() -> Self {
        Self::new("llzk://constrain/executor_timestamp", 0, 0)
    }

    /// Location family for top-level witness SSA expressions lowered into `@compute`.
    pub fn compute_ssa(index: usize) -> Self {
        Self::new("llzk://compute/ssa", index, 0)
    }

    /// Location family for compiler-derived executor timestamp lowering in `@compute`.
    pub fn compute_executor_timestamp() -> Self {
        Self::new("llzk://compute/executor_timestamp", 0, 0)
    }

    /// Location family for runtime hooks used by one witness SSA expression.
    ///
    /// `path` should identify the concrete hook kind (for example
    /// `llzk://compute/runtime/oracle_u32`). The line encodes the zero-based SSA expression
    /// index, while the column remains available for any future substructure within that hook.
    pub const fn compute_runtime(path: &'static str, index: usize) -> Self {
        Self::new(path, index, 0)
    }

    /// Location for a generated struct definition.
    pub fn layout_struct(name: &str) -> Self {
        Self::new_owned(format!("llzk://layout/struct/{name}"), 0, 0)
    }

    /// Location for a generated method on a struct definition.
    pub fn layout_function(struct_name: &str, function_name: &str) -> Self {
        Self::new_owned(
            format!("llzk://layout/function/{struct_name}/{function_name}"),
            0,
            0,
        )
    }

    /// Child location family for a generated function argument label.
    pub fn layout_argument() -> Self {
        Self::new("llzk://layout/argument", 0, 0)
    }

    /// Plain file/line/column location family for a generated function argument label.
    pub fn layout_argument_label(label: &str) -> Self {
        Self::new_owned(format!("llzk://layout/argument/{label}"), 0, 0)
    }

    /// Child location family for a generated struct member label.
    pub fn layout_member() -> Self {
        Self::new("llzk://layout/member", 0, 0)
    }

    /// Plain file/line/column location family for a generated struct member label.
    pub fn layout_member_label(label: &str) -> Self {
        Self::new_owned(format!("llzk://layout/member/{label}"), 0, 0)
    }

    /// Return a sibling location at a later zero-based column within the same semantic line.
    pub fn with_column_offset(self, offset: usize) -> Self {
        Self {
            column: self.column + offset,
            ..self
        }
    }
}

/// Module-scoped helper with convenience factory methods and access to the root LLZK module.
pub struct ModuleEnv<'ctx, F: FieldInfo> {
    context: &'ctx Context,
    /// The root LLZK module.
    module: &'ctx Module<'ctx>,
    debug_location_style: DebugLocationStyle,
    _field: core::marker::PhantomData<F>,
}

impl<'ctx, F: FieldInfo> ModuleEnv<'ctx, F> {
    /// Creates a new module helper.
    pub fn new(
        context: &'ctx Context,
        module: &'ctx Module<'ctx>,
        debug_location_style: DebugLocationStyle,
    ) -> Self {
        Self {
            context,
            module,
            debug_location_style,
            _field: PhantomData,
        }
    }

    /// Returns a reference to the context.
    pub fn context(&self) -> &'ctx Context {
        self.context
    }

    /// Returns a reference to the root module.
    pub fn module(&self) -> &'ctx Module<'ctx> {
        self.module
    }

    /// Returns the unknown location.
    pub fn unknown_location(&self) -> Location<'ctx> {
        Location::unknown(self.context)
    }

    /// Convert a synthetic semantic location into an MLIR file/line/column location.
    pub fn semantic_location(&self, location: SemanticLocation) -> Location<'ctx> {
        Location::new(
            self.context,
            location.path.as_ref(),
            location.line,
            location.column,
        )
    }

    /// Wrap a semantic child location in a descriptive MLIR `NameLoc`.
    pub fn semantic_name_location(&self, name: &str, child: SemanticLocation) -> Location<'ctx> {
        Location::name(self.context, name, self.semantic_location(child))
    }

    /// Emit either a descriptive `NameLoc` or a plain file/line/column location, depending on the
    /// configured debug-location style.
    pub fn semantic_labeled_location(
        &self,
        name: &str,
        named_child: SemanticLocation,
        plain_location: SemanticLocation,
    ) -> Location<'ctx> {
        match self.debug_location_style {
            DebugLocationStyle::Named => self.semantic_name_location(name, named_child),
            DebugLocationStyle::FileLineCol => self.semantic_location(plain_location),
        }
    }

    /// Creates a `!felt.type`.
    pub fn felt_type(&self) -> Type<'ctx> {
        FeltType::with_field(self.context, F::field_name()).into()
    }

    /// Get the index type
    #[inline]
    pub fn index_type(&self) -> Type<'ctx> {
        Type::index(self.context)
    }

    /// Get an integer type
    pub fn int_type(&self, bits: u32) -> Type<'ctx> {
        IntegerType::new(self.context, bits).into()
    }

    /// Get the boolean type (i.e., i1)
    pub fn bool_type(&self) -> Type<'ctx> {
        IntegerType::new(self.context, 1).into()
    }

    /// Get a constant index-type integer attribute
    #[inline]
    pub fn index_attr(&self, integer: i64) -> Attribute<'ctx> {
        self.int_attr(self.index_type(), integer)
    }

    /// Create a constant felt attribute.
    pub fn felt_attr(&self, value: u64) -> FeltConstAttribute<'ctx> {
        FeltConstAttribute::new(self.context, value, Some(F::field_name()))
    }

    /// Create a constant int attribute of the given int type.
    #[inline]
    pub fn int_attr(&self, r#type: Type<'ctx>, integer: i64) -> Attribute<'ctx> {
        IntegerAttribute::new(r#type, integer).into()
    }

    /// Get a register type, which is a two-element felt array.
    /// TODO: This is probably too representation dependent, move elsewhere?
    pub fn register_type(&self) -> Type<'ctx> {
        ArrayType::new(
            self.felt_type(),
            &[self.index_attr(
                i64::try_from(REGISTER_SIZE).expect("REGISTER_SIZE is unexpectedly large"),
            )],
        )
        .into()
    }

    /// Get a one-dimensional array type with static length `len`.
    pub fn felt_array_type(&self, len: usize) -> Result<Type<'ctx>> {
        Ok(ArrayType::new(self.felt_type(), &[self.index_attr(i64::try_from(len)?)]).into())
    }

    /// Declare a private module-level external function if it is not already present.
    ///
    /// Used to create oracle hooks (e.g., ROM reads) for `@compute`.
    pub fn declare_private_extern_function(
        &self,
        name: &str,
        inputs: &[Type<'ctx>],
        results: &[Type<'ctx>],
    ) -> Result<()> {
        if self.module_contains_top_level_function(name)? {
            return Ok(());
        }

        let visibility = [(
            Identifier::new(self.context, "sym_visibility"),
            StringAttribute::new(self.context, "private").into(),
        )];
        let location = Location::new(self.context, &format!("llzk://layout/extern/{name}"), 0, 0);
        let func = dialect::function::def(
            location,
            name,
            FunctionType::new(self.context, inputs, results),
            &visibility,
            None,
        )?;
        self.module.body().append_operation(func.into());
        Ok(())
    }

    /// Query the module for the given named free function.
    fn module_contains_top_level_function(&self, name: &str) -> Result<bool> {
        let module_op = self.module.as_operation();
        let mut found = false;
        module_op.walk(WalkOrder::PreOrder, |op| {
            if op
                .parent_operation()
                .map(|parent| parent == module_op)
                .unwrap_or(false)
            {
                if dialect::function::is_func_def(&op)
                    && op
                        .attribute("sym_name")
                        .and_then(StringAttribute::try_from)
                        .map(|attr| attr.value() == name)
                        .unwrap_or(false)
                {
                    found = true;
                    WalkResult::Interrupt
                } else {
                    // This query only cares about free functions directly under the module.
                    WalkResult::Skip
                }
            } else {
                WalkResult::Advance
            }
        });

        Ok(found)
    }

    /// Return `true` if any operation nested in the module references `callee` through a
    /// `function.call`-style symbol attribute.
    pub fn module_contains_call_to(&self, callee: &str) -> Result<bool> {
        let callee_attr = format!("@{callee}");
        let mut found = false;
        let mut module_op =
            unsafe { OperationRefMut::from_raw(self.module.as_operation().to_raw()) };
        module_op.walk_mut(WalkOrder::PreOrder, |op| {
            if op
                .attribute("callee")
                .map(|attr| attr.to_string().contains(&callee_attr))
                .unwrap_or(false)
            {
                found = true;
                WalkResult::Interrupt
            } else {
                WalkResult::Advance
            }
        });
        Ok(found)
    }
}

/// Possible locations for insertion.
enum InsertionPoint {
    /// Beginning of function.
    Start,
    /// End of function (before the terminator, if any)
    End,
}

/// Key type for caching const op values
#[derive(Debug, Eq, PartialEq)]
pub struct ConstOpKey<'ctx>(Type<'ctx>, u64);

impl<'ctx> Ord for ConstOpKey<'ctx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.1
            .cmp(&other.1)
            .then_with(|| self.0.to_string().cmp(&other.0.to_string()))
    }
}

impl<'ctx> PartialOrd for ConstOpKey<'ctx> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Operations builder that handles insertion of operations in the target function.
pub struct OpsBuilder<'ctx: 'sco, 'sco, F: FieldInfo> {
    env: &'ctx ModuleEnv<'ctx, F>,
    scope: FuncDefOpRef<'ctx, 'sco>,
    /// Cache of constant op values of specified type at the beginning of the
    /// function scope. Using a BTreeMap since [Type] is not hashable.
    const_vals: RefCell<BTreeMap<ConstOpKey<'ctx>, Value<'ctx, 'sco>>>,
    /// Stack of scoped semantic locations. The top entry is the semantic location currently in
    /// effect for emitted ops.
    semantic_locations: RefCell<Vec<SemanticLocation>>,
}

impl<'ctx, 'sco, F: FieldInfo> OpsBuilder<'ctx, 'sco, F> {
    /// Creates a new builder.
    pub fn new(env: &'ctx ModuleEnv<'ctx, F>, scope: FuncDefOpRef<'ctx, 'sco>) -> Self {
        Self {
            scope,
            env,
            const_vals: BTreeMap::new().into(),
            semantic_locations: Vec::new().into(),
        }
    }

    /// Returns the scoped semantic location currently active for this builder, if any.
    pub fn current_semantic_location(&self) -> Option<SemanticLocation> {
        self.semantic_locations.borrow().last().cloned()
    }

    /// Run `f` with `location` as the effective builder location.
    pub fn with_semantic_location<T>(
        &self,
        location: SemanticLocation,
        f: impl FnOnce() -> Result<T>,
    ) -> Result<T> {
        struct SemanticLocationGuard<'a> {
            stack: &'a RefCell<Vec<SemanticLocation>>,
        }

        impl Drop for SemanticLocationGuard<'_> {
            fn drop(&mut self) {
                // Always restore the previous scope, even if lowering returns early.
                self.stack
                    .borrow_mut()
                    .pop()
                    .expect("semantic location stack underflow");
            }
        }

        // Push before running the closure so nested helpers inherit the same semantic location.
        self.semantic_locations.borrow_mut().push(location);
        let _guard = SemanticLocationGuard {
            stack: &self.semantic_locations,
        };
        f()
    }

    /// Run `f` with the current semantic location shifted to a sibling column, if one is active.
    pub fn with_column_offset<T>(&self, offset: usize, f: impl FnOnce() -> Result<T>) -> Result<T> {
        if let Some(location) = self.current_semantic_location() {
            self.with_semantic_location(location.with_column_offset(offset), f)
        } else {
            f()
        }
    }

    /// Returns the currently active semantic location, or `loc(unknown)` when no semantic scope
    /// is active.
    pub fn current_location(&self) -> Location<'ctx> {
        self.current_semantic_location()
            .map(|location| self.env.semantic_location(location))
            .unwrap_or_else(|| self.env.unknown_location())
    }

    /// Compatibility shim for older call sites. Prefer [`Self::current_location`] for new code.
    pub fn unknown_location(&self) -> Location<'ctx> {
        self.current_location()
    }

    /// Appends an operation with no results at the end.
    #[inline]
    pub fn append_op_with_no_results(&self, op: Operation<'ctx>) -> Result<()> {
        let _ = self.insert_operation(InsertionPoint::End, op)?;
        Ok(())
    }

    /// Appends an operation with results at the end.
    #[inline]
    pub fn append_op_with_results<const N: usize>(
        &self,
        op: Operation<'ctx>,
    ) -> Result<[Value<'ctx, 'sco>; N]> {
        let op = self.insert_operation(InsertionPoint::End, op)?;
        self.extract_results(op)
    }

    /// Appends an operation with one result at the end.
    #[inline]
    pub fn append_op_with_result(&self, op: Operation<'ctx>) -> Result<Value<'ctx, 'sco>> {
        self.append_op_with_results::<1>(op).map(|v| v[0])
    }

    /// Inserts an operation with one result at the start.
    #[inline]
    pub fn insert_op_with_result_at_start(&self, op: Operation<'ctx>) -> Result<Value<'ctx, 'sco>> {
        let op = self.insert_operation(InsertionPoint::Start, op)?;
        self.extract_results::<1>(op).map(|v| v[0])
    }

    fn extract_results<const N: usize>(
        &self,
        op: OperationRef<'ctx, 'sco>,
    ) -> Result<[Value<'ctx, 'sco>; N]> {
        op.results()
            .map(Into::into)
            .collect::<Vec<_>>()
            .try_into()
            .map_err(|values: Vec<_>| anyhow!("was expecting {N} results but got {}", values.len()))
    }

    fn first_block(&self) -> Result<BlockRef<'ctx, 'sco>> {
        assert_eq!(self.scope.region_count(), 1);
        self.scope
            .region(0)?
            .first_block()
            .ok_or_else(|| anyhow!("function's region is missing a block"))
    }

    fn last_block(&self) -> Result<BlockRef<'ctx, 'sco>> {
        self.blocks()
            .last()
            .ok_or_else(|| anyhow!("function's region is missing a block"))
    }

    fn blocks(&self) -> impl Iterator<Item = BlockRef<'ctx, 'sco>> {
        std::iter::successors(self.first_block().ok(), |blk: &BlockRef| {
            blk.next_in_region()
        })
    }

    fn extract_insertion_point(
        &self,
        point: InsertionPoint,
    ) -> Result<(Option<OperationRef<'ctx, 'sco>>, BlockRef<'ctx, 'sco>)> {
        Ok(match point {
            InsertionPoint::Start => {
                let blk = self.first_block()?;
                (blk.first_operation(), blk)
            }
            InsertionPoint::End => {
                let blk = self.last_block()?;
                (blk.terminator(), blk)
            }
        })
    }

    /// Generic insertion function. The other insertion functions should be convenience methods over
    /// this one.
    fn insert_operation(
        &self,
        point: InsertionPoint,
        operation: Operation<'ctx>,
    ) -> Result<OperationRef<'ctx, 'sco>> {
        let (point, blk) = self.extract_insertion_point(point)?;
        Ok(match point {
            Some(fst) => blk.insert_operation_before(fst, operation),
            None => blk.append_operation(operation),
        })
    }

    /// Insert a `constrain.eq` operation to constrain `lhs` equal to `rhs`. If
    /// `conditional` is supplied, then the constraint will be `conditional => (lhs === rhs)`
    /// (implemented as `!conditional || (lhs === rhs)` since LLZK has no implication operation).
    #[inline]
    pub fn append_constrain_eq(
        &self,
        location: Location<'ctx>,
        lhs: Value<'ctx, 'sco>,
        rhs: Value<'ctx, 'sco>,
    ) -> Result<()> {
        self.append_op_with_no_results(constrain::eq(location, lhs, rhs))
    }

    /// Insert a `constrain.eq` at the builder's current semantic location.
    #[inline]
    pub fn append_constrain_eq_here(
        &self,
        lhs: Value<'ctx, 'sco>,
        rhs: Value<'ctx, 'sco>,
    ) -> Result<()> {
        self.append_constrain_eq(self.current_location(), lhs, rhs)
    }

    /// If not None, insert a `constrain.eq` operation to constrain `conditional => (lhs === rhs)`
    /// (implemented as `!conditional || (lhs === rhs)` since LLZK has no implication operation).
    /// Assumes `conditional` is a felt.type that is constrained to be in a boolean range.
    /// If `conditional` is None, just inserts a regular equality constraint between `lhs` and
    /// `rhs`.
    pub fn append_conditional_constrain_eq(
        &self,
        location: Location<'ctx>,
        conditional: Option<Value<'ctx, 'sco>>,
        lhs: Value<'ctx, 'sco>,
        rhs: Value<'ctx, 'sco>,
    ) -> Result<()> {
        match conditional {
            None => self.append_constrain_eq(location, lhs, rhs),
            Some(conditional) => {
                let not_conditional = self.append_eq_predicate(
                    location,
                    self.get_felt_constant_from_start(0)?,
                    conditional,
                )?;
                let sides_eq = self.append_eq_predicate(location, lhs, rhs)?;
                let implication =
                    self.append_op_with_result(bool::or(location, not_conditional, sides_eq)?)?;
                let truth = self.get_constant_from_start(self.bool_type(), 1)?;
                self.append_constrain_eq(location, implication, truth)
            }
        }
    }

    /// Insert a conditional `constrain.eq` at the builder's current semantic location.
    #[inline]
    pub fn append_conditional_constrain_eq_here(
        &self,
        conditional: Option<Value<'ctx, 'sco>>,
        lhs: Value<'ctx, 'sco>,
        rhs: Value<'ctx, 'sco>,
    ) -> Result<()> {
        self.append_conditional_constrain_eq(self.current_location(), conditional, lhs, rhs)
    }

    /// Compare `lhs` and `rhs` and return an `i1` predicate.
    ///
    /// LLZK uses different equality ops for felts and plain integer types, so conditional
    /// constraints need this helper instead of assuming every compared value is a felt.
    fn append_eq_predicate(
        &self,
        location: Location<'ctx>,
        lhs: Value<'ctx, 'sco>,
        rhs: Value<'ctx, 'sco>,
    ) -> Result<Value<'ctx, 'sco>> {
        anyhow::ensure!(
            lhs.r#type() == rhs.r#type(),
            "cannot compare values with different types: {} vs {}",
            lhs.r#type(),
            rhs.r#type()
        );

        if lhs.r#type() == self.felt_type() {
            self.append_op_with_result(bool::eq(location, lhs, rhs)?)
        } else if lhs.r#type() == self.index_type() || lhs.r#type().isa::<IntegerType>() {
            self.append_op_with_result(arith::cmpi(
                self.context,
                arith::CmpiPredicate::Eq,
                lhs,
                rhs,
                location,
            ))
        } else {
            anyhow::bail!("unsupported equality predicate type {}", lhs.r#type());
        }
    }

    /// Assert that the given boolean predicate holds inside `@compute`.
    pub fn append_bool_assert(
        &self,
        location: Location<'ctx>,
        predicate: Value<'ctx, 'sco>,
        msg: Option<&str>,
    ) -> Result<()> {
        self.append_op_with_no_results(bool::assert(location, predicate, msg)?)
    }

    /// Compare `lhs` and `rhs` and assert that they are equal inside `@compute`.
    pub fn append_assert_equal(
        &self,
        location: Location<'ctx>,
        lhs: Value<'ctx, 'sco>,
        rhs: Value<'ctx, 'sco>,
        msg: Option<&str>,
    ) -> Result<()> {
        let predicate = self.append_eq_predicate(location, lhs, rhs)?;
        self.append_bool_assert(location, predicate, msg)
    }

    /// Compute the inner values used to generate a boolean constraint.
    /// Used so both the conditional and unconditional constraint variants use
    /// the same logic.
    fn compute_boolean_constraint_expression(
        &self,
        val: Value<'ctx, 'sco>,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        assert_eq!(val.r#type(), self.felt_type());
        let unk = self.unknown_location();
        let zero = self.get_constant_from_start(self.felt_type(), 0)?;
        let one = self.get_constant_from_start(self.felt_type(), 1)?;
        let minus_one = self.append_op_with_result(felt::sub(unk, val, one)?)?;
        let product = self.append_op_with_result(felt::mul(unk, val, minus_one)?)?;
        Ok((product, zero))
    }

    /// Append a boolean constraint for the given value.
    #[inline]
    pub fn append_boolean_constraint(&self, val: Value<'ctx, 'sco>) -> Result<()> {
        let (product, zero) = self.compute_boolean_constraint_expression(val)?;
        self.append_constrain_eq(self.unknown_location(), product, zero)
    }

    /// Append a conditional (if provided) boolean constraint for the given value.
    #[inline]
    pub fn append_conditional_boolean_constraint(
        &self,
        conditional: Option<Value<'ctx, 'sco>>,
        val: Value<'ctx, 'sco>,
    ) -> Result<()> {
        let (product, zero) = self.compute_boolean_constraint_expression(val)?;
        self.append_conditional_constrain_eq(self.unknown_location(), conditional, product, zero)
    }

    /// Compute the inner values ised to generate a range constraint.
    /// Used so both the conditional and unconditioanl constraint variants use the same logic.
    fn compute_range_constraint_expression(
        &self,
        val: Value<'ctx, 'sco>,
        width: usize,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        assert_eq!(val.r#type(), self.felt_type());
        let bound = self.get_constant_from_start(self.felt_type(), 1 << width)?;
        let bound_check =
            self.append_op_with_result(bool::lt(self.unknown_location(), val, bound)?)?;
        let truth = self.get_constant_from_start(self.int_type(1), 1)?;
        Ok((bound_check, truth))
    }

    /// Append a range constraint for the given value.
    /// Enforces that `val` must be within `width`.
    pub fn append_range_constraint(&self, val: Value<'ctx, 'sco>, width: usize) -> Result<()> {
        let (bound_check, truth) = self.compute_range_constraint_expression(val, width)?;
        self.append_constrain_eq(self.unknown_location(), bound_check, truth)
    }

    /// Append a range constraint for the given value.
    /// Enforces that `val` must be within `width` if `conditional` is provided and is true.
    pub fn append_conditional_range_constraint(
        &self,
        conditional: Option<Value<'ctx, 'sco>>,
        val: Value<'ctx, 'sco>,
        width: usize,
    ) -> Result<()> {
        let (bound_check, truth) = self.compute_range_constraint_expression(val, width)?;
        self.append_conditional_constrain_eq(
            self.unknown_location(),
            conditional,
            bound_check,
            truth,
        )
    }

    /// Get the value from the contained function scope.
    pub fn get_arg_value(&self, arg_no: usize) -> Result<Value<'ctx, 'sco>> {
        Ok(self.scope.argument(arg_no)?.into())
    }

    /// Return the struct instance created at the start of a `@compute` body.
    pub fn get_compute_self_value(&self) -> Result<Value<'ctx, 'sco>> {
        // LLZK exposes this directly on the function op, conveniently
        Ok(self.scope.self_value_of_compute()?)
    }

    /// Append a struct member read operation in the current function scope.
    pub fn append_member_read(
        &self,
        location: Location<'ctx>,
        component: Value<'ctx, 'sco>,
        result_type: Type<'ctx>,
        member_name: &str,
    ) -> Result<Value<'ctx, 'sco>> {
        let op = r#struct::readm(
            &OpBuilder::new(self.context),
            location,
            result_type,
            component,
            member_name,
        )?;
        self.append_op_with_result(op)
    }

    /// Append a struct member read using the builder's current semantic location.
    pub fn append_member_read_here(
        &self,
        component: Value<'ctx, 'sco>,
        result_type: Type<'ctx>,
        member_name: &str,
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_member_read(self.current_location(), component, result_type, member_name)
    }

    /// Append a struct member write operation in the current function scope.
    pub fn append_member_write(
        &self,
        location: Location<'ctx>,
        component: Value<'ctx, 'sco>,
        member_name: &str,
        value: Value<'ctx, 'sco>,
    ) -> Result<()> {
        let op = r#struct::writem(location, component, member_name, value)?;
        self.append_op_with_no_results(op)
    }

    /// Append an uninitialized one-dimensional felt array allocation.
    pub fn append_new_felt_array(
        &self,
        location: Location<'ctx>,
        len: usize,
    ) -> Result<Value<'ctx, 'sco>> {
        let array_ty = ArrayType::try_from(self.felt_array_type(len)?)?;
        self.append_op_with_result(array::new(
            &OpBuilder::new(self.context),
            location,
            array_ty,
            ArrayCtor::Empty,
        ))
    }

    /// Append a one-dimensional felt array initialized from the given values.
    pub fn append_new_felt_array_from_values(
        &self,
        location: Location<'ctx>,
        values: &[Value<'ctx, 'sco>],
    ) -> Result<Value<'ctx, 'sco>> {
        let array_ty = ArrayType::try_from(self.felt_array_type(values.len())?)?;
        self.append_op_with_result(array::new(
            &OpBuilder::new(self.context),
            location,
            array_ty,
            ArrayCtor::Values(values),
        ))
    }

    /// Append an array read operation and return the read value.
    pub fn append_array_read(
        &self,
        location: Location<'ctx>,
        arr_ref: Value<'ctx, 'sco>,
        indices: &[Value<'ctx, 'sco>],
    ) -> Result<Value<'ctx, 'sco>> {
        let arr_ty = ArrayType::try_from(arr_ref.r#type())?;
        self.append_op_with_result(array::read(
            location,
            arr_ty.element_type(),
            arr_ref,
            indices,
        ))
    }

    /// Append an array read using the builder's current semantic location.
    pub fn append_array_read_here(
        &self,
        arr_ref: Value<'ctx, 'sco>,
        indices: &[Value<'ctx, 'sco>],
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_array_read(self.current_location(), arr_ref, indices)
    }

    /// Append an array write operation in the current function scope.
    pub fn append_array_write(
        &self,
        location: Location<'ctx>,
        arr_ref: Value<'ctx, 'sco>,
        indices: &[Value<'ctx, 'sco>],
        rvalue: Value<'ctx, 'sco>,
    ) -> Result<()> {
        self.append_op_with_no_results(array::write(location, arr_ref, indices, rvalue))
    }

    /// Append a `function.call` and return all results.
    pub fn append_call<const N: usize>(
        &self,
        location: Location<'ctx>,
        callee: &str,
        args: &[Value<'ctx, 'sco>],
        result_types: &[Type<'ctx>],
    ) -> Result<[Value<'ctx, 'sco>; N]> {
        let op = dialect::function::call(
            &OpBuilder::new(self.context),
            location,
            FlatSymbolRefAttribute::new(self.context, callee),
            args,
            result_types,
        )?;
        self.append_op_with_results::<N>(op.into())
    }

    /// Append a `function.call` with a single result.
    #[inline]
    pub fn append_call_with_result(
        &self,
        location: Location<'ctx>,
        callee: &str,
        args: &[Value<'ctx, 'sco>],
        result_type: Type<'ctx>,
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_call::<1>(location, callee, args, &[result_type])
            .map(|results| results[0])
    }

    /// Append a `function.call` that returns no results.
    #[inline]
    pub fn append_call_no_results(
        &self,
        location: Location<'ctx>,
        callee: &str,
        args: &[Value<'ctx, 'sco>],
    ) -> Result<()> {
        let op = dialect::function::call(
            &OpBuilder::new(self.context),
            location,
            FlatSymbolRefAttribute::new(self.context, callee),
            args,
            &[] as &[Type<'ctx>],
        )?;
        self.append_op_with_no_results(op.into())
    }

    /// Lookup a previously generated constant in the function scope or
    /// create one if needed. Then return the SSA value.
    pub fn get_constant_from_start(&self, r#type: Type<'ctx>, i: u64) -> Result<Value<'ctx, 'sco>> {
        let key = ConstOpKey(r#type, i);
        let mut const_val_cache = self.const_vals.borrow_mut();
        match const_val_cache.get(&key) {
            Some(v) => Ok(*v),
            None => {
                let const_op = if r#type == self.index_type() || r#type.isa::<IntegerType>() {
                    arith::constant(
                        self.context,
                        self.int_attr(r#type, i64::try_from(i)?),
                        self.unknown_location(),
                    )
                } else if r#type == self.felt_type() {
                    felt::constant(self.unknown_location(), self.felt_attr(i))?
                } else {
                    anyhow::bail!("unsupported type {}", r#type)
                };
                let v = self.insert_op_with_result_at_start(const_op)?;
                anyhow::ensure!(
                    const_val_cache.insert(key, v).is_none(),
                    "replaced existing index const value in function preamble"
                );
                Ok(v)
            }
        }
    }

    /// Get a `felt.type` constant from the function prologue.
    #[inline]
    pub fn get_felt_constant_from_start(&self, i: u64) -> Result<Value<'ctx, 'sco>> {
        self.get_constant_from_start(self.felt_type(), i)
    }

    /// Get an `i1` constant from the function prologue.
    #[inline]
    pub fn get_bool_constant_from_start(&self, value: bool) -> Result<Value<'ctx, 'sco>> {
        self.get_constant_from_start(self.bool_type(), value as u64)
    }

    /// Perform the index constant insertion without producing a return value.
    pub fn insert_constant_at_start(&self, r#type: Type<'ctx>, i: u64) -> Result<()> {
        let _ = self.get_constant_from_start(r#type, i)?;
        Ok(())
    }

    /// Create a new nondet value of the specified type.
    #[inline]
    pub fn new_nondet(&self, r#type: Type<'ctx>) -> Result<Value<'ctx, 'sco>> {
        self.append_op_with_result(llzk::dialect::llzk::nondet(self.unknown_location(), r#type))
    }

    /// Create a new nondet felt.
    #[inline]
    pub fn new_nondet_felt(&self) -> Result<Value<'ctx, 'sco>> {
        self.new_nondet(self.felt_type())
    }

    /// Fold the given values using the binary operation provided.
    fn append_fold<FN>(
        &self,
        location: Location<'ctx>,
        operation_fn: FN,
        values: &[Value<'ctx, 'sco>],
    ) -> Result<Value<'ctx, 'sco>>
    where
        FN: Fn(
            Location<'ctx>,
            Value<'ctx, 'sco>,
            Value<'ctx, 'sco>,
        ) -> Result<Operation<'ctx>, llzk::error::Error>,
    {
        values
            .iter()
            .map(|v| Ok(*v))
            .reduce(|acc, v| {
                let add = operation_fn(location, acc?, v?)?;
                self.append_op_with_result(add)
            })
            .ok_or_else(|| anyhow!("must provide values to append_fold"))?
    }

    /// Perform addition using `felt.add` over all specified values.
    #[inline]
    pub fn append_sum(
        &self,
        location: Location<'ctx>,
        values: &[Value<'ctx, 'sco>],
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_fold::<_>(location, felt::add, values)
    }

    /// Perform addition using `felt.add` over all specified values at the current location.
    #[inline]
    pub fn append_sum_here(&self, values: &[Value<'ctx, 'sco>]) -> Result<Value<'ctx, 'sco>> {
        self.append_sum(self.current_location(), values)
    }

    /// Perform multiplication using `felt.mul` over all specified values.
    #[inline]
    pub fn append_product(
        &self,
        location: Location<'ctx>,
        values: &[Value<'ctx, 'sco>],
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_fold::<_>(location, felt::mul, values)
    }

    /// Perform multiplication using `felt.mul` over all specified values at the current location.
    #[inline]
    pub fn append_product_here(&self, values: &[Value<'ctx, 'sco>]) -> Result<Value<'ctx, 'sco>> {
        self.append_product(self.current_location(), values)
    }

    /// Emit a generic `arith.select`, which works for both LLZK felts and builtin integer types.
    pub fn append_select_value(
        &self,
        condition: Value<'ctx, 'sco>,
        if_true: Value<'ctx, 'sco>,
        if_false: Value<'ctx, 'sco>,
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_op_with_result(arith::select(
            condition,
            if_true,
            if_false,
            self.unknown_location(),
        ))
    }

    /// Return an `i1` indicating whether the felt value is non-zero.
    pub fn append_field_is_nonzero(&self, value: Value<'ctx, 'sco>) -> Result<Value<'ctx, 'sco>> {
        self.append_op_with_result(bool::ne(
            self.unknown_location(),
            value,
            self.get_felt_constant_from_start(0)?,
        )?)
    }

    /// Convert an `i1` condition into the felt encoding used by witness columns.
    pub fn append_bool_to_field(&self, value: Value<'ctx, 'sco>) -> Result<Value<'ctx, 'sco>> {
        self.append_select_value(
            value,
            self.get_felt_constant_from_start(1)?,
            self.get_felt_constant_from_start(0)?,
        )
    }

    /// Reduce a felt value modulo `2^bits`.
    pub fn append_lowest_bits_felt(
        &self,
        value: Value<'ctx, 'sco>,
        bits: u32,
    ) -> Result<Value<'ctx, 'sco>> {
        if bits == 0 {
            return self.get_felt_constant_from_start(0);
        }
        let modulus = 1u64 << bits;
        self.append_op_with_result(felt::umod(
            self.unknown_location(),
            value,
            self.get_felt_constant_from_start(modulus)?,
        )?)
    }

    /// Compare a felt-encoded small integer against a literal.
    pub fn append_field_eq_constant(
        &self,
        value: Value<'ctx, 'sco>,
        constant: u64,
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_op_with_result(bool::eq(
            self.unknown_location(),
            value,
            self.get_felt_constant_from_start(constant)?,
        )?)
    }

    /// Sum one-hot equality checks for `value` against a fixed set of small constants.
    pub fn append_field_eq_any_constant(
        &self,
        value: Value<'ctx, 'sco>,
        constants: &[u16],
    ) -> Result<Value<'ctx, 'sco>> {
        let location = self.unknown_location();
        let matches = constants
            .iter()
            .map(|constant| {
                self.append_bool_to_field(
                    self.append_field_eq_constant(value, u64::from(*constant))?,
                )
            })
            .collect::<Result<Vec<_>>>()?;

        if matches.is_empty() {
            self.get_felt_constant_from_start(0)
        } else if matches.len() == 1 {
            Ok(matches[0])
        } else {
            self.append_sum(location, &matches)
        }
    }

    /// Compute the `(is_supported, is_for_delegation)` outputs for the
    /// `SpecialCSRProperties` table.
    pub fn append_special_csr_properties_outputs(
        &self,
        csr_index: Value<'ctx, 'sco>,
        metadata: &SpecialCsrPropertiesMetadata,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let is_for_delegation =
            self.append_field_eq_any_constant(csr_index, &metadata.delegation_indices)?;
        let is_supported = if metadata.supported_only_indices.is_empty() {
            is_for_delegation
        } else {
            self.append_sum(
                location,
                &[
                    self.append_field_eq_any_constant(csr_index, &metadata.supported_only_indices)?,
                    is_for_delegation,
                ],
            )?
        };
        Ok((is_supported, is_for_delegation))
    }

    /// Extract a small bit-slice from a felt-encoded value.
    pub fn append_shifted_low_bits(
        &self,
        value: Value<'ctx, 'sco>,
        shift: u64,
        bits: u32,
    ) -> Result<Value<'ctx, 'sco>> {
        let shifted = if shift == 0 {
            value
        } else {
            self.append_op_with_result(felt::shr(
                self.unknown_location(),
                value,
                self.get_felt_constant_from_start(shift)?,
            )?)?
        };
        self.append_lowest_bits_felt(shifted, bits)
    }

    /// Compute the `(out_low, out_high)` outputs for the `ExtendLoadedValue` table.
    pub fn append_extend_loaded_value_outputs(
        &self,
        input: Value<'ctx, 'sco>,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let word = self.append_lowest_bits_felt(input, 16)?;
        let use_high_half =
            self.append_field_is_nonzero(self.append_shifted_low_bits(input, 16, 1)?)?;
        let funct3 = self.append_shifted_low_bits(input, 17, 3)?;
        let low_byte = self.append_lowest_bits_felt(word, 8)?;
        let high_byte = self.append_shifted_low_bits(word, 8, 8)?;
        let selected_byte = self.append_select_value(use_high_half, high_byte, low_byte)?;
        let byte_sign =
            self.append_field_is_nonzero(self.append_shifted_low_bits(selected_byte, 7, 1)?)?;
        let word_sign = self.append_field_is_nonzero(self.append_shifted_low_bits(word, 15, 1)?)?;
        let zero = self.get_felt_constant_from_start(0)?;
        let full_sign = self.get_felt_constant_from_start(0xffff)?;
        let byte_high_fill = self.get_felt_constant_from_start(0xff00)?;

        let out_low = self.append_select_value(
            self.append_field_eq_constant(funct3, 0b000)?,
            self.append_select_value(
                byte_sign,
                self.append_sum(location, &[selected_byte, byte_high_fill])?,
                selected_byte,
            )?,
            self.append_select_value(
                self.append_field_eq_constant(funct3, 0b100)?,
                selected_byte,
                self.append_select_value(
                    self.append_field_eq_constant(funct3, 0b001)?,
                    word,
                    self.append_select_value(
                        self.append_field_eq_constant(funct3, 0b101)?,
                        word,
                        zero,
                    )?,
                )?,
            )?,
        )?;
        let out_high = self.append_select_value(
            self.append_field_eq_constant(funct3, 0b000)?,
            self.append_select_value(byte_sign, full_sign, zero)?,
            self.append_select_value(
                self.append_field_eq_constant(funct3, 0b001)?,
                self.append_select_value(word_sign, full_sign, zero)?,
                zero,
            )?,
        )?;

        Ok((out_low, out_high))
    }

    /// Compute the output for the `StoreByteSourceContribution` table.
    pub fn append_store_byte_source_contribution_output(
        &self,
        byte: Value<'ctx, 'sco>,
        bit_0: Value<'ctx, 'sco>,
    ) -> Result<Value<'ctx, 'sco>> {
        let location = self.unknown_location();
        let shifted = self.append_op_with_result(felt::shl(
            location,
            byte,
            self.get_felt_constant_from_start(8)?,
        )?)?;
        let bit_0_bool = self.append_field_is_nonzero(bit_0)?;
        self.append_select_value(bit_0_bool, shifted, byte)
    }

    /// Compute the output for the `StoreByteExistingContribution` table.
    pub fn append_store_byte_existing_contribution_output(
        &self,
        word: Value<'ctx, 'sco>,
        bit_0: Value<'ctx, 'sco>,
    ) -> Result<Value<'ctx, 'sco>> {
        let location = self.unknown_location();
        let keep_low = self.append_op_with_result(felt::bit_and(
            location,
            word,
            self.get_felt_constant_from_start(0x00ff)?,
        )?)?;
        let keep_high = self.append_op_with_result(felt::bit_and(
            location,
            word,
            self.get_felt_constant_from_start(0xff00)?,
        )?)?;
        let bit_0_bool = self.append_field_is_nonzero(bit_0)?;
        self.append_select_value(bit_0_bool, keep_low, keep_high)
    }

    /// Compute the `(in_place, overflow)` outputs for the `ShiftImplementation` table.
    pub fn append_shift_implementation_outputs(
        &self,
        input: Value<'ctx, 'sco>,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let word = self.append_lowest_bits_felt(input, 16)?;
        let shift_amount = self.append_shifted_low_bits(input, 16, 5)?;
        let is_right = self.append_field_is_nonzero(self.append_shifted_low_bits(input, 21, 1)?)?;
        let input_high = self.append_op_with_result(felt::shl(
            location,
            word,
            self.get_felt_constant_from_start(16)?,
        )?)?;
        let right_shifted =
            self.append_op_with_result(felt::shr(location, input_high, shift_amount)?)?;
        let left_shifted = self.append_op_with_result(felt::shl(location, word, shift_amount)?)?;
        let in_place = self.append_select_value(
            is_right,
            self.append_shifted_low_bits(right_shifted, 16, 16)?,
            self.append_lowest_bits_felt(left_shifted, 16)?,
        )?;
        let overflow = self.append_select_value(
            is_right,
            self.append_lowest_bits_felt(right_shifted, 16)?,
            self.append_shifted_low_bits(left_shifted, 16, 16)?,
        )?;
        Ok((in_place, overflow))
    }

    /// Select the 32-bit sign-fill mask for a five-bit shift amount.
    pub fn append_u32_mask_from_shift_amount(
        &self,
        shift_amount: Value<'ctx, 'sco>,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let mut selected_low = self.get_felt_constant_from_start(0)?;
        let mut selected_high = self.get_felt_constant_from_start(0)?;

        for shift in 1u32..32 {
            let mask = u32::MAX << (32 - shift);
            let case = self.append_field_eq_constant(shift_amount, u64::from(shift))?;
            selected_low = self.append_select_value(
                case,
                self.get_felt_constant_from_start(u64::from(mask & 0xffff))?,
                selected_low,
            )?;
            selected_high = self.append_select_value(
                case,
                self.get_felt_constant_from_start(u64::from(mask >> 16))?,
                selected_high,
            )?;
        }

        Ok((selected_low, selected_high))
    }

    /// Compute the `(low, high)` outputs for the `SRASignFiller` table.
    pub fn append_sra_sign_filler_outputs(
        &self,
        input: Value<'ctx, 'sco>,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let sign = self.append_field_is_nonzero(self.append_lowest_bits_felt(input, 1)?)?;
        let is_sra = self.append_field_is_nonzero(self.append_shifted_low_bits(input, 1, 1)?)?;
        let shift_amount = self.append_shifted_low_bits(input, 2, 5)?;
        let apply_fill = self.append_op_with_result(bool::and(
            location,
            sign,
            self.append_op_with_result(bool::and(
                location,
                is_sra,
                self.append_field_is_nonzero(shift_amount)?,
            )?)?,
        )?)?;
        let (mask_low, mask_high) = self.append_u32_mask_from_shift_amount(shift_amount)?;

        Ok((
            self.append_select_value(apply_fill, mask_low, self.get_felt_constant_from_start(0)?)?,
            self.append_select_value(apply_fill, mask_high, self.get_felt_constant_from_start(0)?)?,
        ))
    }

    /// Compute the `(should_branch, should_store)` outputs for the
    /// `ConditionalOpAllConditionsResolver` table.
    pub fn append_conditional_op_all_conditions_outputs(
        &self,
        input: Value<'ctx, 'sco>,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let funct3 = self.append_lowest_bits_felt(input, 3)?;
        let unsigned_lt =
            self.append_field_is_nonzero(self.append_shifted_low_bits(input, 3, 1)?)?;
        let eq = self.append_field_is_nonzero(self.append_shifted_low_bits(input, 4, 1)?)?;
        let src1_sign = self.append_field_is_nonzero(self.append_shifted_low_bits(input, 5, 1)?)?;
        let src2_sign = self.append_field_is_nonzero(self.append_shifted_low_bits(input, 6, 1)?)?;
        let sign_diff = self.append_op_with_result(bool::or(
            location,
            self.append_op_with_result(bool::and(
                location,
                src1_sign,
                self.append_op_with_result(bool::not(location, src2_sign)?)?,
            )?)?,
            self.append_op_with_result(bool::and(
                location,
                self.append_op_with_result(bool::not(location, src1_sign)?)?,
                src2_sign,
            )?)?,
        )?)?;
        let signed_lt = self.append_select_value(sign_diff, src1_sign, unsigned_lt)?;
        let false_bool = self.get_bool_constant_from_start(false)?;
        let expected_branch = self.append_select_value(
            self.append_field_eq_constant(funct3, 0b000)?,
            eq,
            self.append_select_value(
                self.append_field_eq_constant(funct3, 0b001)?,
                self.append_op_with_result(bool::not(location, eq)?)?,
                self.append_select_value(
                    self.append_field_eq_constant(funct3, 0b100)?,
                    signed_lt,
                    self.append_select_value(
                        self.append_field_eq_constant(funct3, 0b101)?,
                        self.append_op_with_result(bool::not(location, signed_lt)?)?,
                        self.append_select_value(
                            self.append_field_eq_constant(funct3, 0b110)?,
                            unsigned_lt,
                            self.append_select_value(
                                self.append_field_eq_constant(funct3, 0b111)?,
                                self.append_op_with_result(bool::not(location, unsigned_lt)?)?,
                                false_bool,
                            )?,
                        )?,
                    )?,
                )?,
            )?,
        )?;
        let expected_store = self.append_select_value(
            self.append_field_eq_constant(funct3, 0b010)?,
            signed_lt,
            self.append_select_value(
                self.append_field_eq_constant(funct3, 0b011)?,
                unsigned_lt,
                false_bool,
            )?,
        )?;

        Ok((
            self.append_bool_to_field(expected_branch)?,
            self.append_bool_to_field(expected_store)?,
        ))
    }

    /// Compute the `(low, high)` outputs for the generic 16-bit logical shift tables.
    pub fn append_logical_shift_16_bit_outputs<
        const INPUT_IS_HIGH: bool,
        const IS_RIGHT_SHIFT: bool,
    >(
        &self,
        input: Value<'ctx, 'sco>,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let word = self.append_lowest_bits_felt(input, 16)?;
        let shift_amount = self.append_shifted_low_bits(input, 16, 5)?;
        let reconstructed = if INPUT_IS_HIGH {
            self.append_op_with_result(felt::shl(
                location,
                word,
                self.get_felt_constant_from_start(16)?,
            )?)?
        } else {
            word
        };
        let shifted = if IS_RIGHT_SHIFT {
            self.append_op_with_result(felt::shr(location, reconstructed, shift_amount)?)?
        } else {
            self.append_op_with_result(felt::shl(location, word, shift_amount)?)?
        };

        Ok((
            self.append_lowest_bits_felt(shifted, 16)?,
            self.append_shifted_low_bits(shifted, 16, 16)?,
        ))
    }

    /// Compute the `(low, high)` outputs for the `Sra16BitInputSignFill` table.
    pub fn append_sra_16_bit_input_sign_fill_outputs(
        &self,
        input: Value<'ctx, 'sco>,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let word = self.append_lowest_bits_felt(input, 16)?;
        let shift_amount = self.append_shifted_low_bits(input, 16, 5)?;
        let sign = self.append_field_is_nonzero(self.append_shifted_low_bits(word, 15, 1)?)?;
        let apply_fill = self.append_op_with_result(bool::and(
            location,
            sign,
            self.append_field_is_nonzero(shift_amount)?,
        )?)?;
        let (expected_low, expected_high) = self.append_u32_mask_from_shift_amount(shift_amount)?;

        Ok((
            self.append_select_value(
                apply_fill,
                expected_low,
                self.get_felt_constant_from_start(0)?,
            )?,
            self.append_select_value(
                apply_fill,
                expected_high,
                self.get_felt_constant_from_start(0)?,
            )?,
        ))
    }

    /// Append a multiplication by the given constant felt value using `felt.mul`.
    pub fn append_const_scaling(
        &self,
        location: Location<'ctx>,
        const_coeff: u64,
        val: Value<'ctx, 'sco>,
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_op_with_result(felt::mul(
            location,
            self.get_felt_constant_from_start(const_coeff)?,
            val,
        )?)
    }

    /// Append a multiplication by the given constant felt value at the current location.
    pub fn append_const_scaling_here(
        &self,
        const_coeff: u64,
        val: Value<'ctx, 'sco>,
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_const_scaling(self.current_location(), const_coeff, val)
    }

    /// Create a vector of N `felt.type` nondets constrained such that:
    /// - They are all boolean
    /// - Only one of them is 1 (i.e., one bit hot)
    pub fn append_one_hot(
        &self,
        location: Location<'ctx>,
        bits: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        let bits = (0..bits)
            .map(|_| {
                let bit = self.new_nondet_felt()?;
                self.append_boolean_constraint(bit)?;
                Ok(bit)
            })
            .collect::<Result<Vec<Value<'ctx, 'sco>>>>()?;
        let sum = self.append_sum(location, &bits)?;
        self.append_op_with_no_results(constrain::eq(
            location,
            sum,
            self.get_felt_constant_from_start(1)?,
        ))?;
        Ok(bits)
    }

    /// Create a one-hot vector at the current semantic location.
    pub fn append_one_hot_here(&self, bits: usize) -> Result<Vec<Value<'ctx, 'sco>>> {
        self.append_one_hot(self.current_location(), bits)
    }

    /// Convert a one-hot bit vector into the original single value.
    pub fn append_one_hot_reconstruction(
        &self,
        location: Location<'ctx>,
        bits: &[Value<'ctx, 'sco>],
    ) -> Result<Value<'ctx, 'sco>> {
        let (_, res) = bits
            .iter()
            .enumerate()
            .map(|(i, v)| Ok((i, *v)))
            .reduce(
                |a: Result<(usize, Value<'ctx, 'sco>)>, x: Result<(usize, Value<'ctx, 'sco>)>| {
                    let (_, acc) = a?;
                    let (i, bit) = x?;
                    let new_val = self.append_sum(
                        location,
                        &[
                            acc,
                            self.append_product(
                                location,
                                &[self.get_felt_constant_from_start(u64::try_from(i)?)?, bit],
                            )?,
                        ],
                    )?;
                    Ok((i, new_val))
                },
            )
            .ok_or_else(|| anyhow!("must provide non-empty bits slice"))??;
        Ok(res)
    }

    /// Reconstruct a one-hot vector at the current semantic location.
    pub fn append_one_hot_reconstruction_here(
        &self,
        bits: &[Value<'ctx, 'sco>],
    ) -> Result<Value<'ctx, 'sco>> {
        self.append_one_hot_reconstruction(self.current_location(), bits)
    }
}

impl<'ctx, 'sco, F: FieldInfo> Deref for OpsBuilder<'ctx, 'sco, F> {
    type Target = ModuleEnv<'ctx, F>;

    fn deref(&self) -> &Self::Target {
        self.env
    }
}

/// Macro for casting a `Result<T, E>` into `Result<Operation, E>` where `T: Into<Operation>`
macro_rules! as_op {
    ($op:expr) => {
        $op.map(Operation::from)
    };
}

#[derive(Clone, Copy)]
struct StructInput<'ctx> {
    r#type: Type<'ctx>,
    location: Option<Location<'ctx>>,
}

struct StructMember<'ctx> {
    name: String,
    r#type: Type<'ctx>,
    is_public: bool,
    location: Option<Location<'ctx>>,
    is_signal: bool,
}

/// Builder for creating structs.
pub struct StructBuilder<'ctx, 'str, F: FieldInfo> {
    /// Shared module-scoped helper used for type construction and module insertion.
    env: &'ctx ModuleEnv<'ctx, F>,
    /// Location for the struct definition itself.
    location: Option<Location<'ctx>>,
    /// Location for the generated `@compute` function.
    compute_location: Option<Location<'ctx>>,
    /// Location for the generated `@constrain` function.
    constrain_location: Option<Location<'ctx>>,
    /// Name of the struct.
    name: &'str str,
    /// Inputs shared by both `@compute` and `@constrain` (excluding `self` in `@constrain`).
    inputs: Vec<StructInput<'ctx>>,
    /// Members together with their public/signal classification.
    members: Vec<StructMember<'ctx>>,
}

impl<'ctx, 'str, F: FieldInfo> StructBuilder<'ctx, 'str, F> {
    /// Creates a new builder.
    pub fn new(env: &'ctx ModuleEnv<'ctx, F>, name: &'str str) -> Self {
        Self {
            env,
            location: None,
            compute_location: None,
            constrain_location: None,
            name,
            inputs: vec![],
            members: vec![],
        }
    }

    /// Adds an input with an explicit debug location.
    pub fn with_input_location(
        &mut self,
        input: Type<'ctx>,
        location: Location<'ctx>,
    ) -> &mut Self {
        self.inputs.push(StructInput {
            r#type: input,
            location: Some(location),
        });
        self
    }

    /// Sets the location of the struct.
    pub fn with_location(&mut self, location: Location<'ctx>) -> &mut Self {
        self.location = Some(location);
        self
    }

    /// Sets the location of the generated `@compute` function.
    pub fn with_compute_location(&mut self, location: Location<'ctx>) -> &mut Self {
        self.compute_location = Some(location);
        self
    }

    /// Sets the location of the generated `@constrain` function.
    pub fn with_constrain_location(&mut self, location: Location<'ctx>) -> &mut Self {
        self.constrain_location = Some(location);
        self
    }

    /// Adds a member with an explicit debug location.
    pub fn with_member_location(
        &mut self,
        name: String,
        r#type: Type<'ctx>,
        is_public: bool,
        location: Location<'ctx>,
    ) -> &mut Self {
        self.members.push(StructMember {
            name,
            r#type,
            is_public,
            location: Some(location),
            is_signal: false,
        });
        self
    }

    /// Adds a member that corresponds to a proof-system signal.
    pub fn with_signal_member(
        &mut self,
        name: String,
        r#type: Type<'ctx>,
        is_public: bool,
    ) -> &mut Self {
        self.members.push(StructMember {
            name,
            r#type,
            is_public,
            location: None,
            is_signal: true,
        });
        self
    }

    /// Adds a signal member with an explicit debug location.
    pub fn with_signal_member_location(
        &mut self,
        name: String,
        r#type: Type<'ctx>,
        is_public: bool,
        location: Location<'ctx>,
    ) -> &mut Self {
        self.members.push(StructMember {
            name,
            r#type,
            is_public,
            location: Some(location),
            is_signal: true,
        });
        self
    }

    /// Create the struct type for this struct builder.
    fn struct_type(&self) -> StructType<'ctx> {
        StructType::from_str(self.context(), self.name)
    }

    fn location(&self) -> Location<'ctx> {
        self.location
            .unwrap_or_else(|| Location::unknown(self.context()))
    }

    fn compute_location(&self) -> Location<'ctx> {
        self.compute_location.unwrap_or_else(|| self.location())
    }

    fn constrain_location(&self) -> Location<'ctx> {
        self.constrain_location.unwrap_or_else(|| self.location())
    }

    /// Creates a struct using the build data.
    pub fn build(&self) -> Result<StructDefOp<'ctx>, LlzkError> {
        let constrain_inputs = self
            .inputs
            .iter()
            .map(|input| {
                (
                    input.r#type,
                    input.location.unwrap_or_else(|| self.constrain_location()),
                )
            })
            .collect::<Vec<_>>();
        let compute_inputs = self
            .inputs
            .iter()
            .map(|input| {
                (
                    input.r#type,
                    input.location.unwrap_or_else(|| self.compute_location()),
                )
            })
            .collect::<Vec<_>>();
        let members = self.members.iter().map(|member| {
            let mut op = dialect::r#struct::member(
                member.location.unwrap_or_else(|| self.location()),
                &member.name,
                member.r#type,
                true,
                member.is_public,
            )?;
            if member.is_signal {
                op.set_attribute("signal", Attribute::unit(self.context()));
            }
            Ok(Operation::from(op))
        });

        let compute = as_op!(dialect::r#struct::helpers::compute_fn(
            self.compute_location(),
            self.struct_type(),
            &compute_inputs,
            None,
        ));
        let constrain = as_op!(dialect::r#struct::helpers::constrain_fn(
            self.constrain_location(),
            self.struct_type(),
            &constrain_inputs,
            None,
        ));

        dialect::r#struct::def(
            self.location(),
            self.name,
            std::iter::chain(members, [compute, constrain]),
        )
    }

    /// Builds the struct, inserts it into the module, then returns a reference to it.
    pub fn build_in_module(&self) -> Result<StructDefOpRef<'ctx, 'ctx>, LlzkError> {
        let op = self.build()?;
        let op_ref = self.module().body().append_operation(op.into());
        op_ref.try_into()
    }
}

impl<'ctx, 'str, F: FieldInfo> Deref for StructBuilder<'ctx, 'str, F> {
    type Target = ModuleEnv<'ctx, F>;

    fn deref(&self) -> &Self::Target {
        self.env
    }
}

#[cfg(test)]
impl<'ctx, 'str, F: FieldInfo> StructBuilder<'ctx, 'str, F> {
    /// Adds an input to the list.
    pub fn with_input(&mut self, input: Type<'ctx>) -> &mut Self {
        self.inputs.push(StructInput {
            r#type: input,
            location: None,
        });
        self
    }

    /// Adds a member to the struct.
    pub fn with_member(&mut self, name: String, r#type: Type<'ctx>, is_public: bool) -> &mut Self {
        self.members.push(StructMember {
            name,
            r#type,
            is_public,
            location: None,
            is_signal: false,
        });
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use llzk::operation::verify_operation_with_diags;
    use melior::ir::operation::OperationPrintingFlags;
    use prover::field::Mersenne31Field;

    fn count_named_top_level_functions(module: &Module<'_>, name: &str) -> usize {
        let mut count = 0;
        let mut current = module.body().first_operation();
        while let Some(op) = current {
            if dialect::function::is_func_def(&op)
                && op
                    .attribute("sym_name")
                    .and_then(StringAttribute::try_from)
                    .map(|attr| attr.value() == name)
                    .unwrap_or(false)
            {
                count += 1;
            }
            current = op.next_in_block();
        }
        count
    }

    #[test]
    fn module_contains_top_level_function_ignores_nested_struct_functions() {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);

        let builder = StructBuilder::new(&env, "nested_fns_only");
        module
            .body()
            .append_operation(builder.build().unwrap().into());

        assert!(!env.module_contains_top_level_function("compute").unwrap());
        assert!(!env.module_contains_top_level_function("constrain").unwrap());

        env.declare_private_extern_function("top_level_hook", &[], &[])
            .unwrap();
        assert!(env
            .module_contains_top_level_function("top_level_hook")
            .unwrap());

        verify_operation_with_diags(&module.as_operation()).unwrap();
    }

    #[test]
    fn declare_private_extern_function_is_idempotent() {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);
        let felt = env.felt_type();

        env.declare_private_extern_function("read_oracle_field", &[felt], &[felt])
            .unwrap();
        env.declare_private_extern_function("read_oracle_field", &[felt], &[felt])
            .unwrap();

        assert_eq!(
            count_named_top_level_functions(&module, "read_oracle_field"),
            1
        );
        assert!(env
            .module_contains_top_level_function("read_oracle_field")
            .unwrap());

        verify_operation_with_diags(&module.as_operation()).unwrap();
    }

    #[test]
    fn semantic_location_uses_virtual_llzk_paths() {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);

        let location =
            env.semantic_location(SemanticLocation::constrain_constraint(3).with_column_offset(2));
        assert_eq!(
            location.to_string(),
            "loc(\"llzk://constrain/constraints\":3:2)"
        );

        let location = env.semantic_location(SemanticLocation::compute_ssa(5));
        assert_eq!(location.to_string(), "loc(\"llzk://compute/ssa\":5:0)");

        let location = env.semantic_location(SemanticLocation::compute_runtime(
            "llzk://compute/runtime/oracle_u32",
            5,
        ));
        assert_eq!(
            location.to_string(),
            "loc(\"llzk://compute/runtime/oracle_u32\":5:0)"
        );

        let location =
            env.semantic_name_location("Variable(30)", SemanticLocation::layout_argument());
        assert_eq!(
            location.to_string(),
            "loc(\"Variable(30)\"(\"llzk://layout/argument\":0:0))"
        );
    }

    #[test]
    fn struct_builder_marks_signal_inputs_and_members() {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);
        let mut builder = StructBuilder::new(&env, "signal_attrs");
        let felt = env.felt_type();

        builder.with_input(felt);
        builder.with_signal_member("sig_member".to_string(), felt, false);
        builder.with_member("tmp_member".to_string(), felt, false);
        let struct_op = builder.build_in_module().unwrap();
        let sig_member = struct_op.get_member_def("sig_member").unwrap();

        let ir = module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new())
            .unwrap();

        assert!(sig_member.attribute("signal").is_ok());
        assert!(ir.contains("signal"));
        verify_operation_with_diags(&module.as_operation()).unwrap();
    }
}
