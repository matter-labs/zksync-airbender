#[allow(unused_variables)]
fn eval_fn_1<'a, 'b: 'a, W: WitnessTypeSet<BabyBearField>, P: WitnessProxy<BabyBearField, W> + 'b>(
    witness_proxy: &'a mut P,
) where
    W::Field: Copy,
    W::Mask: Copy,
    W::U32: Copy,
    W::U16: Copy,
    W::U8: Copy,
    W::I32: Copy,
{
    let v_0 = witness_proxy.get_oracle_value_u32(Placeholder::ExternalOracle);
    let v_1 = witness_proxy.get_memory_place_u16(22usize);
    let v_2 = witness_proxy.get_memory_place_u16(23usize);
    let v_3 = witness_proxy.get_witness_place_u16(0usize);
    let v_4 = witness_proxy.get_witness_place_u16(1usize);
    let v_5 = witness_proxy.get_witness_place_boolean(2usize);
    let v_6 = witness_proxy.get_witness_place_boolean(3usize);
    let v_7 = witness_proxy.get_witness_place_boolean(4usize);
    let v_8 = witness_proxy.get_witness_place_boolean(5usize);
    let v_9 = witness_proxy.get_witness_place_boolean(6usize);
    let v_10 = witness_proxy.get_witness_place_boolean(7usize);
    let v_11 = witness_proxy.get_witness_place_boolean(9usize);
    let v_12 = witness_proxy.get_memory_place_u8(2usize);
    let v_13 = witness_proxy.get_memory_place_u8(3usize);
    let v_14 = witness_proxy.get_memory_place_u8(4usize);
    let v_15 = witness_proxy.get_memory_place_u8(5usize);
    let v_16 = witness_proxy.get_memory_place_u8(9usize);
    let v_17 = witness_proxy.get_memory_place_u8(10usize);
    let v_18 = witness_proxy.get_memory_place_u8(11usize);
    let v_19 = witness_proxy.get_memory_place_u8(12usize);
    let v_20 = v_15.widen();
    let v_21 = v_20.shl(8u32);
    let v_22 = v_14.widen();
    let mut v_23 = v_21;
    W::U16::add_assign(&mut v_23, &v_22);
    let v_24 = v_23.widen();
    let v_25 = v_24.shl(16u32);
    let v_26 = v_13.widen();
    let v_27 = v_26.shl(8u32);
    let v_28 = v_12.widen();
    let mut v_29 = v_27;
    W::U16::add_assign(&mut v_29, &v_28);
    let v_30 = v_29.widen();
    let mut v_31 = v_25;
    W::U32::add_assign(&mut v_31, &v_30);
    let v_32 = W::Field::from_integer(v_31);
    let v_33 = v_19.widen();
    let v_34 = v_33.shl(8u32);
    let v_35 = v_18.widen();
    let mut v_36 = v_34;
    W::U16::add_assign(&mut v_36, &v_35);
    let v_37 = v_36.widen();
    let v_38 = v_37.shl(16u32);
    let v_39 = v_17.widen();
    let v_40 = v_39.shl(8u32);
    let v_41 = v_16.widen();
    let mut v_42 = v_40;
    W::U16::add_assign(&mut v_42, &v_41);
    let v_43 = v_42.widen();
    let mut v_44 = v_38;
    W::U32::add_assign(&mut v_44, &v_43);
    let v_45 = W::Field::from_integer(v_44);
    let mut v_46 = v_32;
    W::Field::mul_assign(&mut v_46, &v_45);
    let v_47 = v_46.as_integer();
    let v_48 = W::U32::constant(2013265921u32);
    let mut v_49 = v_47;
    W::U32::sub_assign(&mut v_49, &v_48);
    let mut v_50 = v_32;
    W::Field::sub_assign(&mut v_50, &v_45);
    let v_51 = v_50.as_integer();
    let mut v_52 = v_51;
    W::U32::sub_assign(&mut v_52, &v_48);
    let mut v_53 = v_32;
    W::Field::add_assign(&mut v_53, &v_45);
    let v_54 = v_53.as_integer();
    let mut v_55 = v_54;
    W::U32::sub_assign(&mut v_55, &v_48);
    let v_56 = W::U32::constant(0u32);
    let v_57 = WitnessComputationCore::select(&v_8, &v_55, &v_56);
    let v_58 = WitnessComputationCore::select(&v_9, &v_52, &v_57);
    let v_59 = WitnessComputationCore::select(&v_10, &v_49, &v_58);
    let v_60 = v_59.truncate();
    witness_proxy.set_witness_place_u16(10usize, v_60);
    let v_62 = v_59.shr(16u32);
    let v_63 = v_62.truncate();
    witness_proxy.set_witness_place_u16(11usize, v_63);
    let v_65 = v_47.truncate();
    let v_66 = W::U16::constant(1u16);
    let v_67 = W::U16::overflowing_sub(&v_65, &v_66).1;
    let v_68 = v_51.truncate();
    let v_69 = W::U16::overflowing_sub(&v_68, &v_66).1;
    let v_70 = v_54.truncate();
    let v_71 = W::U16::overflowing_sub(&v_70, &v_66).1;
    let v_72 = W::U16::overflowing_add(&v_1, &v_3).1;
    let v_73 = W::U16::overflowing_sub(&v_29, &v_42).1;
    let mut v_74 = v_29;
    W::U16::sub_assign(&mut v_74, &v_42);
    let v_75 = W::U16::overflowing_sub(&v_74, &v_3).1;
    let v_76 = W::Mask::or(&v_73, &v_75);
    let v_77 = W::U16::overflowing_add(&v_29, &v_42).1;
    let mut v_78 = v_29;
    W::U16::add_assign(&mut v_78, &v_42);
    let v_79 = W::U16::overflowing_add(&v_78, &v_3).1;
    let v_80 = W::Mask::or(&v_77, &v_79);
    let v_81 = W::Mask::constant(false);
    let v_82 = W::Mask::select(&v_5, &v_80, &v_81);
    let v_83 = W::Mask::select(&v_6, &v_76, &v_82);
    let v_84 = W::Mask::select(&v_7, &v_72, &v_83);
    let v_85 = W::Mask::select(&v_8, &v_71, &v_84);
    let v_86 = W::Mask::select(&v_9, &v_69, &v_85);
    let v_87 = W::Mask::select(&v_10, &v_67, &v_86);
    witness_proxy.set_witness_place_boolean(12usize, v_87);
    let v_89 = W::U32::overflowing_sub(&v_47, &v_48).1;
    let v_90 = W::U32::overflowing_sub(&v_51, &v_48).1;
    let v_91 = W::U32::overflowing_sub(&v_54, &v_48).1;
    let v_92 = v_2.widen();
    let v_93 = v_92.shl(16u32);
    let v_94 = v_1.widen();
    let mut v_95 = v_93;
    W::U32::add_assign(&mut v_95, &v_94);
    let v_96 = v_4.widen();
    let v_97 = v_96.shl(16u32);
    let v_98 = v_3.widen();
    let mut v_99 = v_97;
    W::U32::add_assign(&mut v_99, &v_98);
    let v_100 = W::U32::overflowing_add(&v_95, &v_99).1;
    let v_101 = W::U32::overflowing_sub(&v_31, &v_44).1;
    let v_102 = W::U32::overflowing_add(&v_31, &v_44).1;
    let mut v_103 = v_31;
    W::U32::add_assign(&mut v_103, &v_44);
    let v_104 = W::U32::overflowing_add(&v_103, &v_99).1;
    let v_105 = W::Mask::or(&v_102, &v_104);
    let v_106 = W::Mask::select(&v_5, &v_105, &v_81);
    let v_107 = W::Mask::select(&v_6, &v_101, &v_106);
    let v_108 = W::Mask::select(&v_7, &v_100, &v_107);
    let v_109 = W::Mask::select(&v_8, &v_91, &v_108);
    let v_110 = W::Mask::select(&v_9, &v_90, &v_109);
    let v_111 = W::Mask::select(&v_10, &v_89, &v_110);
    let v_112 = W::Mask::select(&v_11, &v_81, &v_111);
    witness_proxy.set_witness_place_boolean(13usize, v_112);
    witness_proxy.set_witness_place(14usize, v_46);
}
#[allow(dead_code)]
pub fn evaluate_witness_fn<
    'a,
    'b: 'a,
    W: WitnessTypeSet<BabyBearField>,
    P: WitnessProxy<BabyBearField, W> + 'b,
>(
    witness_proxy: &'a mut P,
) where
    W::Field: Copy,
    W::Mask: Copy,
    W::U32: Copy,
    W::U16: Copy,
    W::U8: Copy,
    W::I32: Copy,
{
    eval_fn_1(witness_proxy);
}
