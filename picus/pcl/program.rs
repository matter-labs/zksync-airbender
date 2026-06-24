use crate::pcl::expr::PicusConstraint;
use crate::pcl::expr::PicusExpr;
use crate::pcl::partial_evaluate;
use crate::pcl::partial_evaluate_calls;
use std::collections::BTreeMap;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::{self};
use std::fs::File;
use std::io::Write;
use std::io::{self};
use std::path::Path;

/// A call to another Picus module (by name).
///
/// Renders to the PCL s-expression:
///
/// ```text
/// (call [<outputs...>] <mod_name> [<inputs...>])
/// ```
///
/// where both `outputs` and `inputs` are printed using `Display` for `PicusExpr`,
/// enclosed in `[...]` and space-separated.
#[derive(Debug, Clone, Default)]
pub struct PicusCall {
    /// Callee module name. This will oftentimes be specialized (e.g., suffixed with constants)
    /// by the compiler to facilitate partial evaluation of the callee.
    pub mod_name: String,
    /// Expressions that *receive* the callee results at the call site.
    /// (Printed first in the call s-expression.)
    pub outputs: Vec<PicusExpr>,
    /// Expressions that are *passed* to the callee.
    /// (Printed last in the call s-expression.)
    pub inputs: Vec<PicusExpr>,
}

impl PicusCall {
    pub fn new(mod_name: String, outputs: &[PicusExpr], inputs: &[PicusExpr]) -> PicusCall {
        PicusCall {
            mod_name,
            outputs: outputs.into(),
            inputs: inputs.into(),
        }
    }

    pub fn apply_multiplier(&self, multiplier: PicusExpr) -> PicusCall {
        let new_inputs: Vec<PicusExpr> = self
            .inputs
            .iter()
            .map(|x| multiplier.clone() * (*x).clone())
            .collect();
        PicusCall {
            mod_name: self.mod_name.clone(),
            outputs: self.outputs.clone(),
            inputs: new_inputs,
        }
    }
}

/// A single Picus module and its contents.
///
/// A module has a name, a list of input/output expressions (ports),
/// a set of constraints, optional postconditions, assumptions about
/// determinism, and a list of nested calls to other modules.
///
/// The textual form emitted by [`PicusModule::dump`] is a sequence
/// of PCL s-expressions wrapped between `(begin-module <name>)` and
/// `(end-module)`.
#[derive(Debug, Clone, Default)]
pub struct PicusModule {
    /// Module identifier used in `(begin-module <name>)`.
    pub name: String,
    /// Module inputs (printed as `(input <expr>)`).
    pub inputs: Vec<PicusExpr>,
    /// Module outputs (printed as `(output <expr>)`).
    pub outputs: Vec<PicusExpr>,
    /// Circuit constraints enforced within the module (printed as `(assert <constraint>)`).
    pub constraints: Vec<PicusConstraint>,
    /// Constraints to be treated as postconditions (printed as `(post-condition <constraint>)`).
    pub postconditions: Vec<PicusConstraint>,
    /// Expressions assumed to be deterministic (printed as `(assume-deterministic <expr>)`).
    pub assume_deterministic: Vec<PicusExpr>,
    /// Nested calls emitted inside the module body.
    pub calls: Vec<PicusCall>,
}

impl PicusModule {
    /// Construct an empty Picus module with the given `name`.
    #[must_use]
    pub fn new(name: String) -> Self {
        PicusModule {
            name,
            inputs: Vec::new(),
            outputs: Vec::new(),
            constraints: Vec::new(),
            postconditions: Vec::new(),
            assume_deterministic: Vec::new(),
            calls: Vec::new(),
        }
    }

    /// builds an empty picus module with `num_inputs` inputs and `num_outputs` outputs
    pub fn build_empty(name: String, num_inputs: usize, num_outputs: usize) -> Self {
        let mut inputs = Vec::with_capacity(num_inputs);
        let mut outputs = Vec::with_capacity(num_inputs);
        for i in 0..num_inputs {
            inputs.push(PicusExpr::Var(i));
        }
        for i in 0..num_outputs {
            outputs.push(PicusExpr::Var(num_inputs + i));
        }
        PicusModule {
            name,
            inputs,
            outputs,
            constraints: Vec::new(),
            postconditions: Vec::new(),
            assume_deterministic: Vec::new(),
            calls: Vec::new(),
        }
    }

    // Applies the multiplier across the constraints
    pub fn apply_multiplier(&mut self, multiplier: PicusExpr) {
        let mut constraints = Vec::with_capacity(self.constraints.len());
        let mut post_conditions = Vec::with_capacity(self.postconditions.len());
        let mut calls = Vec::with_capacity(self.calls.len());
        for constraint in &self.constraints {
            constraints.push(constraint.apply_multiplier(multiplier.clone()));
        }

        for call in &self.calls {
            calls.push(call.apply_multiplier(multiplier.clone()));
        }

        for postcond in &self.postconditions {
            post_conditions.push(postcond.apply_multiplier(multiplier.clone()));
        }
        self.constraints = constraints;
        self.postconditions = post_conditions;
        self.calls = calls;
    }

    #[must_use]
    /// Construct a new Picus module by partially evaluating the module's constraints
    /// with the given values
    pub fn partial_eval(&self, env: &BTreeMap<usize, u64>) -> Self {
        let mut name = self.name.clone();
        for (k, v) in env {
            name += &format!("{k}_{v}");
        }
        let constraints = partial_evaluate(&self.constraints, env);
        let calls = partial_evaluate_calls(&self.calls, env);
        let postconditions = partial_evaluate(&self.postconditions, env);
        PicusModule {
            name,
            inputs: self.inputs.clone(),
            outputs: self.outputs.clone(),
            constraints,
            postconditions,
            assume_deterministic: self.assume_deterministic.clone(),
            calls,
        }
    }
}

impl Display for PicusModule {
    /// Serialize this module into a sequence of PCL lines.
    ///
    /// Output shape:
    ///
    /// ```text
    /// (begin-module <name>)
    /// (input <expr>)*
    /// (output <expr>)*
    /// (assert <constraint>)*
    /// (post-condition <constraint>)*
    /// (assume-deterministic <expr>)*
    /// (call [<outs>] <mod> [<ins>])*
    /// (end-module)
    /// ```
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "(begin-module {})", self.name)?;

        for inp in &self.inputs {
            writeln!(f, "(input {inp})")?;
        }
        for out in &self.outputs {
            writeln!(f, "(output {out})")?;
        }
        for c in &self.constraints {
            writeln!(f, "(assert {c})")?;
        }
        for c in &self.postconditions {
            writeln!(f, "(post-condition {c})")?;
        }
        for e in &self.assume_deterministic {
            writeln!(f, "(assume-deterministic {e})")?;
        }
        for call in &self.calls {
            writeln!(f, "{call}")?;
        }

        write!(f, "(end-module)")
    }
}

/// Print a Picus arithmetic expression in PCL s-expression syntax.
///
/// Examples:
///
/// - `Const(5)`         → `5`
/// - `Var("x",1,0)`     → `x_1_0`
/// - `Add(a,b)`         → `(+ a b)`
/// - `Neg(e)`           → `(- e)`
/// - `Pow(2, e)`        → `(pow 2 e)`
impl Display for PicusExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use PicusExpr::Add;
        use PicusExpr::Const;
        use PicusExpr::Div;
        use PicusExpr::Mul;
        use PicusExpr::Neg;
        use PicusExpr::Pow;
        use PicusExpr::Sub;
        use PicusExpr::Var;
        match self {
            Const(v) => write!(f, "{v}"),
            Var(id) => write!(f, "x_{id}"),
            Add(a, b) => write!(f, "(+ {a} {b})"),
            Sub(a, b) => write!(f, "(- {a} {b})"),
            Mul(a, b) => write!(f, "(* {a} {b})"),
            Div(a, b) => write!(f, "(/ {a} {b})"),
            Neg(a) => write!(f, "(- {a})"),
            Pow(c, e) => write!(f, "(pow {c} {e})"),
        }
    }
}

/// Print a Picus logical/relational constraint in PCL s-expression syntax.
///
/// Notes:
/// - Equalities are represented canonically as `(= <expr> 0)`, i.e., `Eq(e)` means `e = 0`.
/// - Composite forms (`=>`, `<=>`, `&&`, `||`, `!`) print recursively using `Display` on nested
///   constraints/expressions.
impl Display for PicusConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use PicusConstraint::And;
        use PicusConstraint::Det;
        use PicusConstraint::Eq;
        use PicusConstraint::Geq;
        use PicusConstraint::Gt;
        use PicusConstraint::Iff;
        use PicusConstraint::Implies;
        use PicusConstraint::Leq;
        use PicusConstraint::Lt;
        use PicusConstraint::Not;
        use PicusConstraint::Or;
        match self {
            Lt(e1, e2) => write!(f, "(< {e1} {e2})"),
            Leq(e1, e2) => write!(f, "(<= {e1} {e2})"),
            Gt(e1, e2) => write!(f, "(> {e1} {e2})"),
            Geq(e1, e2) => write!(f, "(>= {e1} {e2})"),
            Det(e) => write!(f, "(det {e})"),
            Eq(e) => write!(f, "(= {e} 0)"),
            Implies(c1, c2) => write!(f, "(=> {c1} {c2})"),
            Iff(c1, c2) => write!(f, "(<=> {c1} {c2})"),
            Not(c) => write!(f, "(! {c})"),
            And(c1, c2) => write!(f, "(&& {c1} {c2})"),
            Or(c1, c2) => write!(f, "(|| {c1} {c2})"),
        }
    }
}

/// Print a `(call ...)` s-expression for a [`PicusCall`].
///
/// Uses the `Display` implementation of `PicusExpr` for both output and input
/// vectors via [`write_expr_slice`].
impl Display for PicusCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str("(call ")?;
        write_expr_slice(f, &self.outputs)?;
        write!(f, " {}", self.mod_name)?;
        f.write_str(" ")?;
        write_expr_slice(f, &self.inputs)?;
        f.write_str(")")
    }
}

/// Write a slice of expressions as a bracketed, space-separated list.
///
/// Example: `[e1 e2 e3]`.
///
/// This helper relies on `Display` for `PicusExpr`.
fn write_expr_slice(f: &mut Formatter<'_>, exprs: &[PicusExpr]) -> fmt::Result {
    f.write_str("[")?;
    for (i, e) in exprs.iter().enumerate() {
        if i > 0 {
            f.write_str(" ")?;
        }
        write!(f, "{e}")?;
    }
    f.write_str("]")
}

/// A complete Picus program: the prime field and an ordered set of modules.
///
/// The `modules` map is a `BTreeMap` so that serialization is deterministic
/// across runs (keys are emitted in sorted order).
#[derive(Debug, Clone, Default)]
pub struct PicusProgram {
    /// Prime modulus for the field in which all arithmetic takes place.
    /// It is assumed the value is prime.
    prime: u64,
    /// All modules in this program, keyed by module name.
    modules: BTreeMap<String, PicusModule>,
}

impl PicusProgram {
    /// Create a new empty program over the given prime field.
    #[must_use]
    pub fn new(prime: u64) -> Self {
        PicusProgram {
            prime,
            modules: BTreeMap::new(),
        }
    }

    pub fn build(prime: u64) -> Self {
        Self::new(prime)
    }

    /// Move all entries from `modules` into this program.
    ///
    /// This uses `BTreeMap::append`, transferring ownership of all modules
    /// from the argument map and leaving it empty.
    pub fn add_modules(&mut self, modules: &mut BTreeMap<String, PicusModule>) {
        self.modules.append(modules);
    }

    /// Write the serialized program to any `Write` sink.
    pub fn write_to<W: Write>(&self, mut w: W) -> io::Result<()> {
        write!(w, "{self}")
    }

    /// Write the serialized program to `path`, creating parent directories if needed.
    pub fn write_to_path<P: AsRef<Path>>(&self, path: P) -> io::Result<()> {
        let path = path.as_ref();
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let mut f = File::create(path)?;
        self.write_to(&mut f)
    }
}

/// Serialize the whole program into PCL text.
///
/// Output begins with `(prime-number <p>)`, followed by each module’s
/// PCL block separated by a blank line. Module order is stable due to
/// `BTreeMap` key ordering.
impl Display for PicusProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "(prime-number {})", self.prime)?;
        // Separate modules with a single blank line, deterministic order via BTreeMap.
        let mut first = true;
        for m in self.modules.values() {
            if !first {
                writeln!(f)?;
            }
            first = false;
            writeln!(f, "{m}")?;
        }
        Ok(())
    }
}
