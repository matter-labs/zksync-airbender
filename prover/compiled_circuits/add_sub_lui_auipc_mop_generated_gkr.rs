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
    let v_25 = v_16.widen();
    let v_26 = v_25.shl(16u32);
    let v_27 = v_15.widen();
    let mut v_28 = v_26;
    W::U32::add_assign(&mut v_28, &v_27);
    let v_29 = W::Field::from_integer(v_28);
    let mut v_30 = v_24;
    W::Field::mul_assign(&mut v_30, &v_29);
    let v_31 = v_18.widen();
    let v_32 = v_31.shl(16u32);
    let v_33 = v_17.widen();
    let mut v_34 = v_32;
    W::U32::add_assign(&mut v_34, &v_33);
    let v_35 = W::Field::from_integer(v_34);
    let mut v_36 = v_30;
    W::Field::add_assign(&mut v_36, &v_35);
    let v_37 = W::Field::select(&v_11, &v_36, &v_30);
    let v_38 = v_37.as_integer();
    let v_39 = W::U32::constant(2013265921u32);
    let mut v_40 = v_38;
    W::U32::sub_assign(&mut v_40, &v_39);
    let mut v_41 = v_24;
    W::Field::sub_assign(&mut v_41, &v_29);
    let v_42 = v_41.as_integer();
    let mut v_43 = v_42;
    W::U32::sub_assign(&mut v_43, &v_39);
    let mut v_44 = v_24;
    W::Field::add_assign(&mut v_44, &v_29);
    let v_45 = v_44.as_integer();
    let mut v_46 = v_45;
    W::U32::sub_assign(&mut v_46, &v_39);
    let v_47 = W::U32::constant(0u32);
    let v_48 = WitnessComputationCore::select(&v_8, &v_46, &v_47);
    let v_49 = WitnessComputationCore::select(&v_9, &v_43, &v_48);
    let v_50 = WitnessComputationCore::select(&v_19, &v_40, &v_49);
    let v_51 = v_50.truncate();
    witness_proxy.set_witness_place_u16(11usize, v_51);
    let v_53 = v_50.shr(16u32);
    let v_54 = v_53.truncate();
    witness_proxy.set_witness_place_u16(12usize, v_54);
    let v_56 = v_38.truncate();
    let v_57 = W::U16::constant(1u16);
    let v_58 = W::U16::overflowing_sub(&v_56, &v_57).1;
    let v_59 = v_42.truncate();
    let v_60 = W::U16::overflowing_sub(&v_59, &v_57).1;
    let v_61 = v_45.truncate();
    let v_62 = W::U16::overflowing_sub(&v_61, &v_57).1;
    let v_63 = W::U16::overflowing_add(&v_1, &v_3).1;
    let v_64 = W::U16::overflowing_sub(&v_13, &v_15).1;
    let mut v_65 = v_13;
    W::U16::sub_assign(&mut v_65, &v_15);
    let v_66 = W::U16::overflowing_sub(&v_65, &v_3).1;
    let v_67 = W::Mask::or(&v_64, &v_66);
    let v_68 = W::U16::overflowing_add(&v_13, &v_15).1;
    let mut v_69 = v_13;
    W::U16::add_assign(&mut v_69, &v_15);
    let v_70 = W::U16::overflowing_add(&v_69, &v_3).1;
    let v_71 = W::Mask::or(&v_68, &v_70);
    let v_72 = W::Mask::constant(false);
    let v_73 = W::Mask::select(&v_5, &v_71, &v_72);
    let v_74 = W::Mask::select(&v_6, &v_67, &v_73);
    let v_75 = W::Mask::select(&v_7, &v_63, &v_74);
    let v_76 = W::Mask::select(&v_8, &v_62, &v_75);
    let v_77 = W::Mask::select(&v_9, &v_60, &v_76);
    let v_78 = W::Mask::select(&v_19, &v_58, &v_77);
    witness_proxy.set_witness_place_boolean(13usize, v_78);
    let v_80 = W::U32::overflowing_sub(&v_38, &v_39).1;
    let v_81 = W::U32::overflowing_sub(&v_42, &v_39).1;
    let v_82 = W::U32::overflowing_sub(&v_45, &v_39).1;
    let v_83 = v_2.widen();
    let v_84 = v_83.shl(16u32);
    let v_85 = v_1.widen();
    let mut v_86 = v_84;
    W::U32::add_assign(&mut v_86, &v_85);
    let v_87 = v_4.widen();
    let v_88 = v_87.shl(16u32);
    let v_89 = v_3.widen();
    let mut v_90 = v_88;
    W::U32::add_assign(&mut v_90, &v_89);
    let v_91 = W::U32::overflowing_add(&v_86, &v_90).1;
    let v_92 = W::U32::overflowing_sub(&v_23, &v_28).1;
    let v_93 = W::U32::overflowing_add(&v_23, &v_28).1;
    let mut v_94 = v_23;
    W::U32::add_assign(&mut v_94, &v_28);
    let v_95 = W::U32::overflowing_add(&v_94, &v_90).1;
    let v_96 = W::Mask::or(&v_93, &v_95);
    let v_97 = W::Mask::select(&v_5, &v_96, &v_72);
    let v_98 = W::Mask::select(&v_6, &v_92, &v_97);
    let v_99 = W::Mask::select(&v_7, &v_91, &v_98);
    let v_100 = W::Mask::select(&v_8, &v_82, &v_99);
    let v_101 = W::Mask::select(&v_9, &v_81, &v_100);
    let v_102 = W::Mask::select(&v_19, &v_80, &v_101);
    let v_103 = W::Mask::select(&v_12, &v_72, &v_102);
    witness_proxy.set_witness_place_boolean(14usize, v_103);
    witness_proxy.set_witness_place(15usize, v_37);
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
