use super::*;

pub trait MersenneWrapper {
    fn field_struct() -> TokenStream;
    fn complex_struct() -> TokenStream;
    fn quartic_struct() -> TokenStream;

    fn field_one() -> TokenStream;
    fn field_new(value: TokenStream) -> TokenStream;
    fn quartic_zero() -> TokenStream;
    fn quartic_one() -> TokenStream;

    fn add_assign(a: TokenStream, b: TokenStream) -> TokenStream;
    fn sub_assign(a: TokenStream, b: TokenStream) -> TokenStream;
    fn mul_assign(a: TokenStream, b: TokenStream) -> TokenStream;

    fn add_assign_base(a: TokenStream, b: TokenStream) -> TokenStream;
    fn sub_assign_base(a: TokenStream, b: TokenStream) -> TokenStream;
    fn mul_assign_by_base(a: TokenStream, b: TokenStream) -> TokenStream;

    fn negate(a: TokenStream) -> TokenStream;

    // For ConstraintSystem in circuits
    fn generic_function_parameters() -> TokenStream;
    fn additional_function_arguments() -> TokenStream;
    fn additional_definition_function_arguments() -> TokenStream;

    // Structures that could differ
    fn proof_aux_values_struct() -> TokenStream;
    fn aux_arguments_boundary_values_struct() -> TokenStream;
}

pub struct DefaultMersenne31Field;

impl MersenneWrapper for DefaultMersenne31Field {
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

    fn negate(a: TokenStream) -> TokenStream {
        quote! { field_ops::negate(&mut #a) }
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
