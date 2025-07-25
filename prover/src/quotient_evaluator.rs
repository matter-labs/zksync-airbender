use super::*;
use std::alloc::Allocator;

use ::field::*;
use cs::one_row_compiler::ColumnAddress;
use cs::one_row_compiler::*;
use fft::field_utils::*;
use fft::GoodAllocator;
use trace_holder::*;
use worker::Worker;

use cs::one_row_compiler::read_value;

pub const NUM_DIFFERENT_DIVISORS: usize = 6;

pub const DIVISOR_EVERYWHERE_EXCEPT_LAST_ROW_INDEX: usize = 0;
pub const DIVISOR_EVERYWHERE_EXCEPT_LAST_TWO_ROWS_INDEX: usize = 1;
pub const DIVISOR_FIRST_ROW_INDEX: usize = 2;
pub const DIVISOR_ONE_BEFORE_LAST_ROW_INDEX: usize = 3;
pub const DIVISOR_LAST_ROW_INDEX: usize = 4;
pub const DIVISOR_LAST_ROW_AND_ZERO_INDEX: usize = 5;

pub const DIVISOR_EVERYWHERE_EXCEPT_LAST_ROW_OFFSET: usize =
    DIVISOR_EVERYWHERE_EXCEPT_LAST_ROW_INDEX * 2;
pub const DIVISOR_EVERYWHERE_EXCEPT_LAST_TWO_ROWS_OFFSET: usize =
    DIVISOR_EVERYWHERE_EXCEPT_LAST_TWO_ROWS_INDEX * 2;
pub const DIVISOR_FIRST_ROW_OFFSET: usize = DIVISOR_FIRST_ROW_INDEX * 2;
pub const DIVISOR_ONE_BEFORE_LAST_ROW_OFFSET: usize = DIVISOR_ONE_BEFORE_LAST_ROW_INDEX * 2;
pub const DIVISOR_LAST_ROW_OFFSET: usize = DIVISOR_LAST_ROW_INDEX * 2;
pub const DIVISOR_LAST_ROW_AND_ZERO_OFFSET: usize = DIVISOR_LAST_ROW_AND_ZERO_INDEX * 2;

pub fn compute_divisors_trace<A: GoodAllocator>(
    trace_len: usize,
    tau: Mersenne31Complex,
    worker: &Worker,
) -> RowMajorTrace<Mersenne31Field, DEFAULT_TRACE_PADDING_MULTIPLE, A> {
    assert!(trace_len.is_power_of_two());
    let omega = domain_generator_for_size::<Mersenne31Complex>(trace_len as u64);
    let trace = RowMajorTrace::new_zeroed_for_size(trace_len, 10, A::default());
    let powers_of_x = materialize_powers_parallel::<_, A>(tau, omega, trace_len, worker);
    let powers_of_x_ref = &powers_of_x;

    let mut vanishing = tau.pow(trace_len as u32);
    vanishing.sub_assign(&Mersenne31Complex::ONE);
    let vanishing = vanishing.inverse().unwrap();
    let omega_inv = omega.inverse().unwrap();
    let mut omega_squared = omega;
    omega_squared.square();
    let omega_inv_squared = omega_squared.inverse().unwrap();

    unsafe {
        worker.scope(trace_len, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let mut trace_view = trace.row_view(range.clone());
                let powers_of_x = &powers_of_x_ref[range];

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    // Prepare batch inversion
                    // We need to invert 4 values per row:
                    // 1. (x - omega^0) for first row divisor
                    // 2. (x - omega^-2) for one before last row divisor
                    // 3. (x - omega^-1) for last row divisor
                    // 4. x for last row and zero divisor

                    let batch_size = chunk_size * 4;
                    let mut to_invert = Vec::with_capacity(batch_size);
                    let mut tmp_buffer = vec![Mersenne31Complex::ZERO; batch_size];

                    // Collect all values to invert
                    for i in 0..chunk_size {
                        let x = powers_of_x[i];

                        // (x - omega^0) = (x - 1)
                        let mut f = x;
                        f.sub_assign_base(&Mersenne31Field::ONE);
                        to_invert.push(f);

                        // (x - omega^-2)
                        let mut oo = x;
                        oo.sub_assign(&omega_inv_squared);
                        to_invert.push(oo);

                        // (x - omega^-1)
                        let mut ll = x;
                        ll.sub_assign(&omega_inv);
                        to_invert.push(ll);

                        // x
                        to_invert.push(x);
                    }

                    // Perform batch inversion
                    batch_inverse_inplace(&mut to_invert, &mut tmp_buffer);

                    // Now distribute the inverted values
                    for i in 0..chunk_size {
                        let trace_view_row: &mut [Mersenne31Field] = trace_view.current_row();
                        let x = powers_of_x[i];
                        let mut dst = trace_view_row.as_mut_ptr().cast::<Mersenne31Complex>();

                        // everywhere except last is (x - omega^-1) / (x^n - 1)
                        let mut t = x;
                        t.sub_assign(&omega_inv);
                        t.mul_assign(&vanishing);
                        dst.write(t);
                        dst = dst.add(1);

                        // everywhere except last two is (x - omega^-1) * (x - omega^-2) / (x^n - 1)
                        let mut tt = x;
                        tt.sub_assign(&omega_inv_squared);
                        tt.mul_assign(&t);
                        dst.write(tt);
                        dst = dst.add(1);

                        // Get inverted values from batch
                        let base_idx = i * 4;

                        // first row is 1 / (x - omega^0)
                        let f_inv = to_invert[base_idx];
                        dst.write(f_inv);
                        dst = dst.add(1);

                        // one before last row is 1/(x - omega^-2)
                        let oo_inv = to_invert[base_idx + 1];
                        dst.write(oo_inv);
                        dst = dst.add(1);

                        // last row is 1/(x - omega^-1)
                        let ll_inv = to_invert[base_idx + 2];
                        dst.write(ll_inv);
                        dst = dst.add(1);

                        // and last row and zero are 1 / (x * (x - omega^-1))
                        // ll_inv is already 1/(x - omega^-1), and x_inv is 1/x
                        // so we need: 1 / (x * (x - omega^-1)) = (1/x) * (1/(x - omega^-1)) = x_inv * ll_inv
                        let x_inv = to_invert[base_idx + 3];
                        let mut tmp = x_inv;
                        tmp.mul_assign(&ll_inv);
                        dst.write(tmp);

                        // and go to the next row
                        trace_view.advance_row();
                    }
                });
            }
        });
    }

    trace
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CompiledConstraintsForDomain {
    pub quadratic_terms: Vec<CompiledDegree2ConstraintForDomain>,
    pub linear_terms: Vec<CompiledDegree1ConstraintForDomain>,
    pub tau: Mersenne31Complex,
}

impl CompiledConstraintsForDomain {
    pub fn from_compiled_circuit(
        circuit: &CompiledCircuitArtifact<Mersenne31Field>,
        tau: Mersenne31Complex,
        domain_size: u32,
    ) -> Self {
        assert!(domain_size >= 2);
        assert!(domain_size.is_power_of_two());

        let tau_in_domain_by_half = tau.pow(domain_size as u32 / 2);

        let quadratic_terms = circuit
            .degree_2_constraints
            .iter()
            .map(|el| {
                CompiledDegree2ConstraintForDomain::from_compiled_constraint(
                    el,
                    tau_in_domain_by_half,
                )
            })
            .collect();

        let linear_terms = circuit
            .degree_1_constraints
            .iter()
            .map(|el| {
                CompiledDegree1ConstraintForDomain::from_compiled_constraint(
                    el,
                    tau_in_domain_by_half,
                )
            })
            .collect();

        Self {
            quadratic_terms,
            linear_terms,
            tau,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CompiledDegree2ConstraintForDomain {
    pub quadratic_terms: Box<[(Mersenne31Field, ColumnAddress, ColumnAddress)]>,
    pub linear_terms: Box<[(Mersenne31Complex, ColumnAddress)]>,
    pub constant_term: Mersenne31Complex,
}

impl CompiledDegree2ConstraintForDomain {
    pub fn from_compiled_constraint(
        constraint: &CompiledDegree2Constraint<Mersenne31Field>,
        tau_in_domain_by_half: Mersenne31Complex,
    ) -> Self {
        // (p(x) - c0) / tau^H/2 are in base and we keep them as input, and c0 is made to 0
        // so we will eventually need to multiply every witness value by tau^H/2 to get "true" values on the domain
        // We want to merge multiplication by (tau^H/2)^2 with multiplication by powers of challenges (that are precomputed),
        // so we want to divide lower degree terms enough times
        let tau_in_domain_by_half_inv = tau_in_domain_by_half.inverse().unwrap();

        let quadratic_terms = constraint.quadratic_terms.clone();
        let mut linear_terms = Vec::with_capacity(constraint.quadratic_terms.len());
        for (c, place) in constraint.linear_terms.iter() {
            let mut coeff = tau_in_domain_by_half_inv;
            coeff.mul_assign_by_base(c);
            linear_terms.push((coeff, *place));
        }

        let mut constant_term = tau_in_domain_by_half_inv;
        constant_term.square();
        constant_term.mul_assign_by_base(&constraint.constant_term);

        Self {
            quadratic_terms,
            linear_terms: linear_terms.into_boxed_slice(),
            constant_term,
        }
    }

    pub fn evaluate_at_row(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
    ) -> Mersenne31Complex {
        let mut result = self.constant_term;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = *coeff;
            let var = read_value(*place, witness_row, memory_row);
            value.mul_assign_by_base(&var);
            result.add_assign(&value);
        }

        for (coeff, a, b) in self.quadratic_terms.iter() {
            let mut value = read_value(*a, witness_row, memory_row);
            let b = read_value(*b, witness_row, memory_row);
            value.mul_assign(&b);
            value.mul_assign(coeff);
            result.add_assign_base(&value);
        }

        result
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CompiledDegree1ConstraintForDomain {
    pub linear_terms: Box<[(Mersenne31Field, ColumnAddress)]>,
    pub constant_term: Mersenne31Complex,
}

impl CompiledDegree1ConstraintForDomain {
    pub fn from_compiled_constraint(
        constraint: &CompiledDegree1Constraint<Mersenne31Field>,
        tau_in_domain_by_half: Mersenne31Complex,
    ) -> Self {
        // (p(x) - c0) / tau^H/2 are in base and we keep them as input,
        // so we will eventually need to multiply by tau^H/2 to get "true" values on the domain

        // We want to merge multiplication by tau^H/2 with multiplication by powers of challenges (that are precomputed),
        // so we want to divide lower degree terms enough times
        let tau_in_domain_by_half_inv = tau_in_domain_by_half.inverse().unwrap();

        let linear_terms = constraint.linear_terms.clone();
        let mut constant_term = tau_in_domain_by_half_inv;
        constant_term.mul_assign_by_base(&constraint.constant_term);

        Self {
            linear_terms,
            constant_term,
        }
    }

    pub fn evaluate_at_row(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
    ) -> Mersenne31Complex {
        let mut result = self.constant_term;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign(coeff);
            result.add_assign_base(&value);
        }

        result
    }
}

pub fn evaluate_constraints_on_domain<const N: usize, A: Allocator + Clone>(
    exec_trace: &RowMajorTrace<Mersenne31Field, N, A>,
    num_witness_columns: usize,
    quadratic_terms_challenges: &[Mersenne31Quartic],
    linear_terms_challenges: &[Mersenne31Quartic],
    compiled_constraints_for_domain: &CompiledConstraintsForDomain,
    worker: &Worker,
) -> RowMajorTrace<Mersenne31Field, N, A> {
    assert!(exec_trace.width() >= num_witness_columns);
    let result = RowMajorTrace::new_zeroed_for_size(exec_trace.len(), 4, exec_trace.allocator());

    assert_eq!(
        quadratic_terms_challenges.len(),
        compiled_constraints_for_domain.quadratic_terms.len()
    );
    assert_eq!(
        linear_terms_challenges.len(),
        compiled_constraints_for_domain.linear_terms.len()
    );

    // explicitly skip last row
    let cycles = exec_trace.len() - 1;

    // TODO: adjust by tau^H/2

    worker.scope(cycles, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);

            let range = chunk_start..(chunk_start + chunk_size);
            let mut exec_trace_view = exec_trace.row_view(range.clone());
            let mut quotient_view = result.row_view(range.clone());

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                for _i in 0..chunk_size {
                    let (witness_trace_view_row, memory_trace_view_row) =
                        unsafe { exec_trace_view.current_row_split(num_witness_columns) };
                    let quotient_view_row: &mut [Mersenne31Field] = quotient_view.current_row();

                    let mut quotient_term = Mersenne31Quartic::ZERO;

                    let bound = compiled_constraints_for_domain.quadratic_terms.len();
                    for i in 0..bound {
                        unsafe {
                            let mut challenge = *quadratic_terms_challenges.get_unchecked(i);
                            let term = compiled_constraints_for_domain
                                .quadratic_terms
                                .get_unchecked(i);
                            let term_contribution = term
                                .evaluate_at_row(&*witness_trace_view_row, &*memory_trace_view_row);
                            challenge.mul_assign_by_base(&term_contribution);
                            quotient_term.add_assign(&challenge);
                        }
                    }

                    let bound = compiled_constraints_for_domain.linear_terms.len();
                    for i in 0..bound {
                        unsafe {
                            let mut challenge = *linear_terms_challenges.get_unchecked(i);
                            let term = compiled_constraints_for_domain
                                .linear_terms
                                .get_unchecked(i);
                            let term_contribution = term
                                .evaluate_at_row(&*witness_trace_view_row, &*memory_trace_view_row);
                            challenge.mul_assign_by_base(&term_contribution);
                            quotient_term.add_assign(&challenge);
                        }
                    }

                    let dst_ptr = quotient_view_row.as_mut_ptr().cast::<Mersenne31Quartic>();
                    assert!(dst_ptr.is_aligned());
                    unsafe {
                        dst_ptr.write(quotient_term);
                    }

                    // and go to the next row
                    exec_trace_view.advance_row();
                    quotient_view.advance_row();
                }
            });
        }
    });

    result
}
