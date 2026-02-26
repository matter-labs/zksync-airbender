use std::collections::BTreeMap;

use crate::pcl::current_modulus;
use crate::pcl::reduce_mod;
use crate::pcl::PicusCall;
use crate::pcl::PicusConstraint;
use crate::pcl::PicusExpr;

// === Helpers ===

fn mod_reduce_u64(x: u64) -> u64 {
    // converting to i64 is fine because the prime is 31 bits the input values will not wrap around
    reduce_mod(x as i64)
}

// performs the inverse of `base` with respect to `current_modulus()`
// this is only sound if `modulus` is under `64` bits
fn mod_pow_u64(mut base: u64, mut exp: u64) -> u64 {
    // Fast pow with optional modulus
    if let Some(p) = current_modulus() {
        base %= p;
        let mut acc: u128 = 1;
        let mut b: u128 = base as u128;
        let m: u128 = p as u128;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = (acc * b) % m;
            }
            b = (b * b) % m;
            exp >>= 1;
        }
        acc as u64
    } else {
        // No modulus set: beware overflow
        let mut acc: u128 = 1;
        let mut b: u128 = base as u128;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc.saturating_mul(b);
            }
            b = b.saturating_mul(b);
            exp >>= 1;
        }
        acc as u64
    }
}

// Smart Pow that also folds constants and k=0/1.
fn pow_simplify(k: u64, base: PicusExpr) -> PicusExpr {
    match k {
        0 => 1u64.into(),
        1 => base,
        _ => match base {
            PicusExpr::Const(c) => PicusExpr::Const(mod_pow_u64(c, k)),
            other => PicusExpr::Pow(k, Box::new(other)),
        },
    }
}

// === Expression substitution/simplification ===
// substitutes variables with constants in `e` from `env` and performs partial evaluation
fn subst_expr(e: &PicusExpr, env: &BTreeMap<usize, u64>) -> PicusExpr {
    use crate::PicusExpr::*;
    match e {
        Const(c) => Const(mod_reduce_u64(*c)),
        Var(v) => {
            if let Some(val) = env.get(v) {
                Const(mod_reduce_u64(*val))
            } else {
                Var(*v)
            }
        }
        Add(a, b) => subst_expr(a, env) + subst_expr(b, env),
        Sub(a, b) => subst_expr(a, env) - subst_expr(b, env),
        Mul(a, b) => subst_expr(a, env) * subst_expr(b, env),
        Div(a, b) => {
            // Optional: try to simplify known constants
            let aa = subst_expr(a, env);
            let bb = subst_expr(b, env);
            match (&aa, &bb) {
                (_, Const(1)) => aa,          // e / 1 => e
                (Const(0), _) => 0u64.into(), // 0 / e => 0 (assuming e ≠ 0; safe algebraically)
                _ => Div(Box::new(aa), Box::new(bb)),
            }
        }
        Neg(a) => -subst_expr(a, env),
        Pow(k, a) => pow_simplify(*k, subst_expr(a, env)),
    }
}

// === Call substitution/simplification ===
/// This function replaces variables in `call` with constants in `env`
/// and then simplifies.
pub fn subst_call(call: &PicusCall, env: &BTreeMap<usize, u64>) -> PicusCall {
    let mut new_inputs = Vec::new();
    let mut new_outputs = Vec::new();
    for input in &call.inputs {
        new_inputs.push(subst_expr(input, env));
    }
    for output in &call.outputs {
        new_outputs.push(subst_expr(output, env));
    }
    PicusCall {
        inputs: new_inputs,
        outputs: new_outputs,
        mod_name: call.mod_name.clone(),
    }
}

// === Constraint substitution/simplification ===
/// This function replaces variables in `c` with constants in `env`
/// and then simplifies.
pub fn subst_constraint(
    c: &PicusConstraint,
    env: &BTreeMap<usize, u64>,
) -> Option<PicusConstraint> {
    use PicusConstraint::*;
    let keep = |cc: PicusConstraint| Some(cc);

    match c {
        Eq(e) => {
            let ee = subst_expr(e, env);
            // Drop tautologies Eq(0); keep contradictions as Eq(1)
            match ee {
                PicusExpr::Const(0) => None,
                PicusExpr::Const(1) => keep(Eq(Box::new(1u64.into()))), // 1 = 0 (unsat marker)
                _ => keep(Eq(Box::new(ee))),
            }
        }

        Lt(a, b) => {
            let aa = subst_expr(a, env);
            let bb = subst_expr(b, env);
            match (&aa, &bb) {
                (PicusExpr::Const(x), PicusExpr::Const(y)) => {
                    if x < y {
                        None
                    } else {
                        keep(Eq(Box::new(1u64.into())))
                    }
                }
                _ => keep(Lt(Box::new(aa), Box::new(bb))),
            }
        }

        Leq(a, b) => {
            let aa = subst_expr(a, env);
            let bb = subst_expr(b, env);
            match (&aa, &bb) {
                (PicusExpr::Const(x), PicusExpr::Const(y)) => {
                    if x <= y {
                        None
                    } else {
                        keep(Eq(Box::new(1u64.into())))
                    }
                }
                _ => keep(Leq(Box::new(aa), Box::new(bb))),
            }
        }

        Gt(a, b) => {
            let aa = subst_expr(a, env);
            let bb = subst_expr(b, env);
            match (&aa, &bb) {
                (PicusExpr::Const(x), PicusExpr::Const(y)) => {
                    if x > y {
                        None
                    } else {
                        keep(Eq(Box::new(1u64.into())))
                    }
                }
                _ => keep(Gt(Box::new(aa), Box::new(bb))),
            }
        }

        Geq(a, b) => {
            let aa = subst_expr(a, env);
            let bb = subst_expr(b, env);
            match (&aa, &bb) {
                (PicusExpr::Const(x), PicusExpr::Const(y)) => {
                    if x >= y {
                        None
                    } else {
                        keep(Eq(Box::new(1u64.into())))
                    }
                }
                _ => keep(Geq(Box::new(aa), Box::new(bb))),
            }
        }

        Det(e) => {
            let ee = subst_expr(e, env);
            match ee {
                // Determinism of constants is tautological.
                PicusExpr::Const(_) => None,
                _ => keep(Det(Box::new(ee))),
            }
        }

        Not(p) => {
            // Push inside and simplify:
            match subst_constraint(p, env) {
                None => Some(Eq(Box::new(1u64.into()))), // not(true) => false
                Some(Eq(e)) if matches!(*e, PicusExpr::Const(1)) => None, // not(false) => true
                Some(pp) => Some(Not(Box::new(pp))),
            }
        }

        And(p, q) => {
            let pp = subst_constraint(p, env);
            let qq = subst_constraint(q, env);
            match (pp, qq) {
                (None, None) => None, // true && true
                (Some(Eq(e)), _) if matches!(*e, PicusExpr::Const(1)) => {
                    Some(Eq(Box::new(1u64.into())))
                } // false && _ => false
                (_, Some(Eq(e))) if matches!(*e, PicusExpr::Const(1)) => {
                    Some(Eq(Box::new(1u64.into())))
                }
                (None, Some(r)) => Some(r), // true && r => r
                (Some(l), None) => Some(l),
                (Some(l), Some(r)) => Some(And(Box::new(l), Box::new(r))),
            }
        }

        Or(p, q) => {
            let pp = subst_constraint(p, env);
            let qq = subst_constraint(q, env);
            match (pp, qq) {
                (None, _) => None, // true || _ => true
                (_, None) => None,
                (Some(Eq(e)), r) if matches!(*e, PicusExpr::Const(1)) => r, // false || r => r
                (l, Some(Eq(e))) if matches!(*e, PicusExpr::Const(1)) => l,
                (Some(l), Some(r)) => Some(Or(Box::new(l), Box::new(r))),
            }
        }

        Implies(p, q) => {
            // p => q  ≡  ¬p ∨ q
            let np_or_q = Or(Box::new(Not(p.clone())), q.clone());
            subst_constraint(&np_or_q, env)
        }

        Iff(p, q) => {
            // p <=> q  ≡  (p => q) ∧ (q => p)
            let p_imp_q = Implies(p.clone(), q.clone());
            let q_imp_p = Implies(q.clone(), p.clone());
            subst_constraint(&And(Box::new(p_imp_q), Box::new(q_imp_p)), env)
        }
    }
}

/// Given a collection of constraints `constraints` and a mapping of
/// variables to constants, `partial_evaluate` produces a new set of constraints
/// after substituting those variables with constants and partial evaluating
pub fn partial_evaluate(
    constraints: &[PicusConstraint],
    env: &BTreeMap<usize, u64>,
) -> Vec<PicusConstraint> {
    let mut out_constraints = Vec::with_capacity(constraints.len());
    for c in constraints {
        if let Some(cc) = subst_constraint(c, env) {
            // Optional micro-normalization: if we ever produce Eq(Const(0)) here, drop it
            match &cc {
                PicusConstraint::Eq(e) if matches!(&**e, PicusExpr::Const(0)) => {}
                _ => out_constraints.push(cc),
            }
        }
    }
    out_constraints
}

pub fn partial_evaluate_calls(calls: &[PicusCall], env: &BTreeMap<usize, u64>) -> Vec<PicusCall> {
    let mut out_calls = Vec::with_capacity(calls.len());
    for call in calls {
        out_calls.push(subst_call(call, env))
    }
    out_calls
}
