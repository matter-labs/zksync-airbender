use crate::tables::TableType;

impl quote::ToTokens for TableType {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        use quote::quote;
        let stream = match self {
            TableType::ZeroEntry => quote! { TableType::ZeroEntry },
            TableType::And => quote! { TableType::And },
            TableType::Xor => quote! { TableType::Xor },
            TableType::Or => quote! { TableType::Or },
            TableType::RangeCheck8x8 => quote! { TableType::RangeCheck8x8 },
            TableType::AndNot => quote! { TableType::AndNot },
            TableType::U16GetSignAndHighByte => quote! { TableType::U16GetSignAndHighByte },
            TableType::JumpCleanupOffset => quote! { TableType::JumpCleanupOffset },
            TableType::MemoryOffsetGetBits => quote! { TableType::MemoryOffsetGetBits },
            TableType::MemoryLoadGetSigns => quote! { TableType::MemoryLoadGetSigns },
            // TableType::RomAddressSpaceSeparator => quote! { TableType::RomAddressSpaceSeparator },
            TableType::RomRead => quote! { TableType::RomRead },
            TableType::Xor3 => quote! { TableType::Xor3 },
            TableType::Xor4 => quote! { TableType::Xor4 },
            TableType::Xor7 => quote! { TableType::Xor7 },
            TableType::Xor9 => quote! { TableType::Xor9 },
            TableType::Xor12 => quote! { TableType::Xor12 },
            TableType::RangeCheck9x9 => quote! { TableType::RangeCheck9x9 },
            TableType::RangeCheck10x10 => quote! { TableType::RangeCheck10x10 },
            TableType::RangeCheck11 => quote! { TableType::RangeCheck11 },
            TableType::RangeCheck12 => quote! { TableType::RangeCheck12 },
            TableType::RangeCheck13 => quote! { TableType::RangeCheck13 },
            TableType::U16SelectByteAndGetByteSign => {
                quote! { TableType::U16SelectByteAndGetByteSign }
            }
            TableType::StoreByteSourceContribution => {
                quote! { TableType::StoreByteSourceContribution }
            }
            TableType::StoreByteExistingContribution => {
                quote! { TableType::StoreByteExistingContribution }
            }
            TableType::LoadHalfwordSignextend => {
                quote! { TableType::LoadHalfwordSignextend }
            }
            TableType::LoadByteSignextend => {
                quote! { TableType::LoadByteSignextend }
            }
            TableType::LoadHalfwordRomRead => {
                quote! { TableType::LoadHalfwordRomRead }
            }
            TableType::LoadByteRomRead => {
                quote! { TableType::LoadByteRomRead }
            }
            TableType::ExtendLoadedValue => quote! { TableType::ExtendLoadedValue },
            TableType::AlignedRomRead => quote! { TableType::AlignedRomRead },
            TableType::ConditionalJmpBranchSlt => {
                quote! { TableType::ConditionalJmpBranchSlt }
            }
            TableType::MemStoreClearOriginalRamValueLimb => {
                quote! { TableType::MemStoreClearOriginalRamValueLimb }
            }
            TableType::MemStoreClearWrittenValueLimb => {
                quote! { TableType::MemStoreClearWrittenValueLimb }
            }
            TableType::MemoryGetOffsetAndMaskWithTrap => {
                quote! { TableType::MemoryGetOffsetAndMaskWithTrap }
            }
            TableType::MemoryLoadHalfwordOrByte => quote! { TableType::MemoryLoadHalfwordOrByte },
            TableType::KeccakPermutationIndices => quote!(TableType::KeccakPermutationIndices),
            TableType::XorSpecialIota => quote!(TableType::XorSpecialIota),
            TableType::AndN => quote!(TableType::AndN),
            TableType::RotL => quote!(TableType::RotL),
            TableType::Decoder => quote!(TableType::Decoder),
            TableType::DynamicPlaceholder => {
                unimplemented!("should not appear in final circuits")
            }
            a @ _ => {
                panic!("{:?} is not supported", a);
            }
        };

        tokens.extend(stream);
    }
}
