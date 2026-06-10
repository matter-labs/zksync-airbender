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
    let v_1 = witness_proxy.get_memory_place_u16(18usize);
    let v_2 = witness_proxy.get_memory_place_u16(19usize);
    let v_3 = witness_proxy.get_witness_place_u16(0usize);
    let v_4 = witness_proxy.get_witness_place_u16(1usize);
    let v_5 = witness_proxy.get_witness_place_boolean(2usize);
    let v_6 = witness_proxy.get_witness_place_boolean(3usize);
    let v_7 = witness_proxy.get_witness_place_boolean(4usize);
    let v_8 = witness_proxy.get_witness_place_boolean(5usize);
    let v_9 = witness_proxy.get_witness_place_boolean(6usize);
    let v_10 = witness_proxy.get_witness_place_boolean(7usize);
    let v_11 = witness_proxy.get_witness_place_boolean(8usize);
    let v_12 = witness_proxy.get_witness_place_boolean(10usize);
    let v_13 = witness_proxy.get_memory_place_u16(2usize);
    let v_14 = witness_proxy.get_memory_place_u16(3usize);
    let v_15 = witness_proxy.get_memory_place_u16(7usize);
    let v_16 = witness_proxy.get_memory_place_u16(8usize);
    let v_17 = witness_proxy.get_memory_place_u16(12usize);
    let v_18 = witness_proxy.get_memory_place_u16(13usize);
    let v_19 = W::Mask::or(&v_10, &v_11);
    let v_20 = v_14.widen();
    let v_21 = v_20.shl(16u32);
    let v_22 = v_13.widen();
    let mut v_23 = v_21;
    W::U32::add_assign(&mut v_23, &v_22);
    let v_24 = W::Field::from_integer(v_23);
    let v_25 = W::Field::constant(BabyBearField(1u32));
    let mut v_26 = v_24;
    W::Field::mul_assign(&mut v_26, &v_25);
    let v_27 = v_16.widen();
    let v_28 = v_27.shl(16u32);
    let v_29 = v_15.widen();
    let mut v_30 = v_28;
    W::U32::add_assign(&mut v_30, &v_29);
    let v_31 = W::Field::from_integer(v_30);
    let mut v_32 = v_31;
    W::Field::mul_assign(&mut v_32, &v_25);
    let mut v_33 = v_26;
    W::Field::mul_assign(&mut v_33, &v_32);
    let v_34 = v_18.widen();
    let v_35 = v_34.shl(16u32);
    let v_36 = v_17.widen();
    let mut v_37 = v_35;
    W::U32::add_assign(&mut v_37, &v_36);
    let v_38 = W::Field::from_integer(v_37);
    let mut v_39 = v_38;
    W::Field::mul_assign(&mut v_39, &v_25);
    let mut v_40 = v_33;
    W::Field::add_assign(&mut v_40, &v_39);
    let v_41 = W::Field::select(&v_11, &v_40, &v_33);
    let v_42 = W::Field::constant(BabyBearField(1172168163u32));
    let mut v_43 = v_41;
    W::Field::mul_assign(&mut v_43, &v_42);
    let v_44 = v_43.as_integer();
    let v_45 = W::U32::constant(2013265921u32);
    let mut v_46 = v_44;
    W::U32::sub_assign(&mut v_46, &v_45);
    let mut v_47 = v_24;
    W::Field::sub_assign(&mut v_47, &v_31);
    let v_48 = v_47.as_integer();
    let mut v_49 = v_48;
    W::U32::sub_assign(&mut v_49, &v_45);
    let mut v_50 = v_24;
    W::Field::add_assign(&mut v_50, &v_31);
    let v_51 = v_50.as_integer();
    let mut v_52 = v_51;
    W::U32::sub_assign(&mut v_52, &v_45);
    let v_53 = W::U32::constant(0u32);
    let v_54 = WitnessComputationCore::select(&v_8, &v_52, &v_53);
    let v_55 = WitnessComputationCore::select(&v_9, &v_49, &v_54);
    let v_56 = WitnessComputationCore::select(&v_19, &v_46, &v_55);
    let v_57 = v_56.truncate();
    witness_proxy.set_witness_place_u16(11usize, v_57);
    let v_59 = v_56.shr(16u32);
    let v_60 = v_59.truncate();
    witness_proxy.set_witness_place_u16(12usize, v_60);
    let v_62 = v_44.truncate();
    let v_63 = W::U16::constant(1u16);
    let v_64 = W::U16::overflowing_sub(&v_62, &v_63).1;
    let v_65 = v_48.truncate();
    let v_66 = W::U16::overflowing_sub(&v_65, &v_63).1;
    let v_67 = v_51.truncate();
    let v_68 = W::U16::overflowing_sub(&v_67, &v_63).1;
    let v_69 = W::U16::overflowing_add(&v_1, &v_3).1;
    let v_70 = W::U16::overflowing_sub(&v_13, &v_15).1;
    let mut v_71 = v_13;
    W::U16::sub_assign(&mut v_71, &v_15);
    let v_72 = W::U16::overflowing_sub(&v_71, &v_3).1;
    let v_73 = W::Mask::or(&v_70, &v_72);
    let v_74 = W::U16::overflowing_add(&v_13, &v_15).1;
    let mut v_75 = v_13;
    W::U16::add_assign(&mut v_75, &v_15);
    let v_76 = W::U16::overflowing_add(&v_75, &v_3).1;
    let v_77 = W::Mask::or(&v_74, &v_76);
    let v_78 = W::Mask::constant(false);
    let v_79 = W::Mask::select(&v_5, &v_77, &v_78);
    let v_80 = W::Mask::select(&v_6, &v_73, &v_79);
    let v_81 = W::Mask::select(&v_7, &v_69, &v_80);
    let v_82 = W::Mask::select(&v_8, &v_68, &v_81);
    let v_83 = W::Mask::select(&v_9, &v_66, &v_82);
    let v_84 = W::Mask::select(&v_19, &v_64, &v_83);
    witness_proxy.set_witness_place_boolean(13usize, v_84);
    let v_86 = W::U32::overflowing_sub(&v_44, &v_45).1;
    let v_87 = W::U32::overflowing_sub(&v_48, &v_45).1;
    let v_88 = W::U32::overflowing_sub(&v_51, &v_45).1;
    let v_89 = v_2.widen();
    let v_90 = v_89.shl(16u32);
    let v_91 = v_1.widen();
    let mut v_92 = v_90;
    W::U32::add_assign(&mut v_92, &v_91);
    let v_93 = v_4.widen();
    let v_94 = v_93.shl(16u32);
    let v_95 = v_3.widen();
    let mut v_96 = v_94;
    W::U32::add_assign(&mut v_96, &v_95);
    let v_97 = W::U32::overflowing_add(&v_92, &v_96).1;
    let v_98 = W::U32::overflowing_sub(&v_23, &v_30).1;
    let v_99 = W::U32::overflowing_add(&v_23, &v_30).1;
    let mut v_100 = v_23;
    W::U32::add_assign(&mut v_100, &v_30);
    let v_101 = W::U32::overflowing_add(&v_100, &v_96).1;
    let v_102 = W::Mask::or(&v_99, &v_101);
    let v_103 = W::Mask::select(&v_5, &v_102, &v_78);
    let v_104 = W::Mask::select(&v_6, &v_98, &v_103);
    let v_105 = W::Mask::select(&v_7, &v_97, &v_104);
    let v_106 = W::Mask::select(&v_8, &v_88, &v_105);
    let v_107 = W::Mask::select(&v_9, &v_87, &v_106);
    let v_108 = W::Mask::select(&v_19, &v_86, &v_107);
    let v_109 = W::Mask::select(&v_12, &v_78, &v_108);
    witness_proxy.set_witness_place_boolean(14usize, v_109);
    let v_111 = W::Field::from_integer(v_44);
    witness_proxy.set_witness_place(15usize, v_111);
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
