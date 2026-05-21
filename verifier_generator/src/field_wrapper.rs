use proc_macro2::TokenStream;
use prover::field::PrimeField;
use quote::quote;

pub trait FieldWrapper {
    type BaseField: PrimeField;

    fn coeff_to_internal_repr(coeff: u32) -> u32 {
        Self::BaseField::from_u32_with_reduction(coeff).as_u32_raw_repr_reduced()
    }

    fn field_struct() -> TokenStream;
    fn complex_struct() -> TokenStream;
    fn quartic_struct() -> TokenStream;

    fn field_one() -> TokenStream;
    fn field_new(value: TokenStream) -> TokenStream;
    fn quartic_zero() -> TokenStream;
    fn quartic_one() -> TokenStream;
    fn quartic_from_base(value: TokenStream) -> TokenStream;

    fn add_assign(a: TokenStream, b: TokenStream) -> TokenStream;
    fn sub_assign(a: TokenStream, b: TokenStream) -> TokenStream;
    fn mul_assign(a: TokenStream, b: TokenStream) -> TokenStream;

    fn add_assign_base(a: TokenStream, b: TokenStream) -> TokenStream;
    fn sub_assign_base(a: TokenStream, b: TokenStream) -> TokenStream;
    fn mul_assign_by_base(a: TokenStream, b: TokenStream) -> TokenStream;
    fn add_assign_product_with_base(acc: TokenStream, ext: TokenStream, base: TokenStream) -> TokenStream;

    fn double(a: TokenStream) -> TokenStream;
    fn square(a: TokenStream) -> TokenStream;
    fn negate(a: TokenStream) -> TokenStream;

    /// Convert a raw u32 word to a base field element (from NDS).
    fn field_from_reduced_raw_repr(value: TokenStream) -> TokenStream;
    /// Convert a u32 to a base field element with reduction (from transcript randomness).
    /// Treats the reduced value as raw Montgomery repr, skipping the Montgomery mul.
    fn field_from_raw_repr_with_reduction(value: TokenStream) -> TokenStream;

    // For ConstraintSystem in circuits
    fn generic_function_parameters() -> TokenStream;
    fn additional_function_arguments() -> TokenStream;
    fn additional_definition_function_arguments() -> TokenStream;

    // Structures that could differ
    fn proof_aux_values_struct() -> TokenStream;
    fn aux_arguments_boundary_values_struct() -> TokenStream;

    /// Generate use statements for the field types (base + extension).
    fn field_use_statements() -> TokenStream {
        quote! {}
    }
}

pub struct DefaultBabyBearField;

impl FieldWrapper for DefaultBabyBearField {
    type BaseField = prover::field::baby_bear::base::BabyBearField;

    fn field_struct() -> TokenStream {
        quote! { BabyBearField }
    }

    fn complex_struct() -> TokenStream {
        quote! { BabyBearExt2 }
    }

    fn quartic_struct() -> TokenStream {
        quote! { BabyBearExt4 }
    }

    fn field_one() -> TokenStream {
        quote! { BabyBearField::ONE }
    }

    fn field_new(value: TokenStream) -> TokenStream {
        quote! { BabyBearField::from_reduced_raw_repr(#value) }
    }

    fn quartic_zero() -> TokenStream {
        quote! { BabyBearExt4::ZERO }
    }

    fn quartic_one() -> TokenStream {
        quote! { BabyBearExt4::ONE }
    }

    fn quartic_from_base(value: TokenStream) -> TokenStream {
        quote! { BabyBearExt4::from_base(#value) }
    }

    fn add_assign(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::add_assign(&mut #a, & #b) }
    }

    fn sub_assign(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::sub_assign(&mut #a, & #b) }
    }

    fn mul_assign(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::mul_assign(&mut #a, & #b) }
    }

    fn add_assign_base(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::add_assign_base(&mut #a, & #b) }
    }

    fn sub_assign_base(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::sub_assign_base(&mut #a, & #b) }
    }

    fn mul_assign_by_base(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::mul_assign_by_base(&mut #a, & #b) }
    }

    fn add_assign_product_with_base(a: TokenStream, b: TokenStream, c: TokenStream) -> TokenStream {
        quote! { field_ops::add_assign_product_with_base(&mut #a, & #b, & #c) }
    }

    fn double(a: TokenStream) -> TokenStream {
        quote! { field_ops::double(&mut #a) }
    }

    fn square(a: TokenStream) -> TokenStream {
        quote! { field_ops::square(&mut #a) }
    }

    fn negate(a: TokenStream) -> TokenStream {
        quote! { field_ops::negate(&mut #a) }
    }

    fn field_from_reduced_raw_repr(value: TokenStream) -> TokenStream {
        quote! { BabyBearField::from_reduced_raw_repr(#value) }
    }

    fn field_from_raw_repr_with_reduction(value: TokenStream) -> TokenStream {
        quote! { BabyBearField::from_raw_repr_with_reduction(#value) }
    }

    fn generic_function_parameters() -> TokenStream {
        quote! {}
    }

    fn additional_function_arguments() -> TokenStream {
        quote! {}
    }

    fn additional_definition_function_arguments() -> TokenStream {
        quote! {}
    }

    fn proof_aux_values_struct() -> TokenStream {
        quote! { ProofAuxValues }
    }

    fn aux_arguments_boundary_values_struct() -> TokenStream {
        quote! { AuxArgumentsBoundaryValues }
    }

    fn field_use_statements() -> TokenStream {
        quote! {
            use ::verifier_common::field::baby_bear::base::BabyBearField;
            use ::verifier_common::field::baby_bear::ext4::BabyBearExt4;
        }
    }
}

pub struct DefaultMersenne31Field;

impl FieldWrapper for DefaultMersenne31Field {
    type BaseField = prover::field::Mersenne31Field;

    fn field_struct() -> TokenStream {
        quote! { Mersenne31Field }
    }

    fn complex_struct() -> TokenStream {
        quote! { Mersenne31Complex }
    }

    fn quartic_struct() -> TokenStream {
        quote! { Mersenne31Quartic }
    }

    fn field_one() -> TokenStream {
        quote! { Mersenne31Field::ONE }
    }

    fn field_new(value: TokenStream) -> TokenStream {
        quote! { Mersenne31Field(#value) }
    }

    fn quartic_zero() -> TokenStream {
        quote! { Mersenne31Quartic::ZERO }
    }

    fn quartic_one() -> TokenStream {
        quote! { Mersenne31Quartic::ONE }
    }

    fn quartic_from_base(value: TokenStream) -> TokenStream {
        quote! { Mersenne31Quartic::from_base(#value) }
    }

    fn add_assign(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::add_assign(&mut #a, & #b) }
    }

    fn sub_assign(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::sub_assign(&mut #a, & #b) }
    }

    fn mul_assign(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::mul_assign(&mut #a, & #b) }
    }

    fn add_assign_base(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::add_assign_base(&mut #a, & #b) }
    }

    fn sub_assign_base(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::sub_assign_base(&mut #a, & #b) }
    }

    fn mul_assign_by_base(a: TokenStream, b: TokenStream) -> TokenStream {
        quote! { field_ops::mul_assign_by_base(&mut #a, & #b) }
    }

    fn add_assign_product_with_base(a: TokenStream, b: TokenStream, c: TokenStream) -> TokenStream {
        todo!();
    }

    fn double(a: TokenStream) -> TokenStream {
        quote! { field_ops::double(&mut #a) }
    }

    fn square(a: TokenStream) -> TokenStream {
        quote! { field_ops::square(&mut #a) }
    }

    fn negate(a: TokenStream) -> TokenStream {
        quote! { field_ops::negate(&mut #a) }
    }

    fn field_from_reduced_raw_repr(value: TokenStream) -> TokenStream {
        quote! { Mersenne31Field(#value) }
    }

    fn field_from_raw_repr_with_reduction(value: TokenStream) -> TokenStream {
        quote! { Mersenne31Field::from_raw_repr_with_reduction(#value) }
    }

    fn generic_function_parameters() -> TokenStream {
        quote! {}
    }

    fn additional_function_arguments() -> TokenStream {
        quote! {}
    }

    fn additional_definition_function_arguments() -> TokenStream {
        quote! {}
    }

    fn proof_aux_values_struct() -> TokenStream {
        quote! { ProofAuxValues }
    }

    fn aux_arguments_boundary_values_struct() -> TokenStream {
        quote! { AuxArgumentsBoundaryValues }
    }
}
