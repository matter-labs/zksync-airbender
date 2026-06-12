#[allow(unused_variables)]
fn eval_fn_3<'a, 'b: 'a, W: WitnessTypeSet<BabyBearField>, P: WitnessProxy<BabyBearField, W> + 'b>(
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
    let v_1 = witness_proxy.get_memory_place_u16(26usize);
    let v_2 = witness_proxy.get_memory_place_u16(27usize);
    let v_3 = witness_proxy.get_witness_place_u16(2usize);
    let v_4 = witness_proxy.get_witness_place_u16(3usize);
    let v_5 = witness_proxy.get_witness_place_boolean(5usize);
    let v_6 = witness_proxy.get_witness_place_boolean(6usize);
    let v_7 = witness_proxy.get_witness_place_boolean(7usize);
    let v_8 = witness_proxy.get_witness_place_boolean(8usize);
    let v_9 = witness_proxy.get_witness_place_boolean(9usize);
    let v_10 = witness_proxy.get_witness_place_boolean(10usize);
    let v_11 = witness_proxy.get_witness_place_boolean(11usize);
    let v_12 = witness_proxy.get_witness_place_boolean(13usize);
    let v_13 = witness_proxy.get_memory_place_u8(2usize);
    let v_14 = witness_proxy.get_memory_place_u8(3usize);
    let v_15 = witness_proxy.get_memory_place_u8(4usize);
    let v_16 = witness_proxy.get_memory_place_u8(5usize);
    let v_17 = witness_proxy.get_memory_place_u8(9usize);
    let v_18 = witness_proxy.get_memory_place_u8(10usize);
    let v_19 = witness_proxy.get_memory_place_u8(11usize);
    let v_20 = witness_proxy.get_memory_place_u8(12usize);
    let v_21 = witness_proxy.get_memory_place_u16(18usize);
    let v_22 = witness_proxy.get_memory_place_u16(19usize);
    let v_23 = W::Mask::or(&v_5, &v_6);
    let v_24 = W::Mask::or(&v_23, &v_7);
    let v_25 = W::Mask::or(&v_24, &v_8);
    let v_26 = W::Mask::or(&v_25, &v_9);
    let v_27 = W::Mask::or(&v_26, &v_10);
    let v_28 = W::Mask::or(&v_27, &v_11);
    let v_29 = W::Mask::constant(false);
    let v_30 = W::Mask::or(&v_10, &v_11);
    let v_31 = v_16.widen();
    let v_32 = v_31.shl(8u32);
    let v_33 = v_15.widen();
    let mut v_34 = v_32;
    W::U16::add_assign(&mut v_34, &v_33);
    let v_35 = v_34.widen();
    let v_36 = v_35.shl(16u32);
    let v_37 = v_14.widen();
    let v_38 = v_37.shl(8u32);
    let v_39 = v_13.widen();
    let mut v_40 = v_38;
    W::U16::add_assign(&mut v_40, &v_39);
    let v_41 = v_40.widen();
    let mut v_42 = v_36;
    W::U32::add_assign(&mut v_42, &v_41);
    let v_43 = W::Field::from_raw_repr_with_reduction(v_42);
    let v_44 = v_20.widen();
    let v_45 = v_44.shl(8u32);
    let v_46 = v_19.widen();
    let mut v_47 = v_45;
    W::U16::add_assign(&mut v_47, &v_46);
    let v_48 = v_47.widen();
    let v_49 = v_48.shl(16u32);
    let v_50 = v_18.widen();
    let v_51 = v_50.shl(8u32);
    let v_52 = v_17.widen();
    let mut v_53 = v_51;
    W::U16::add_assign(&mut v_53, &v_52);
    let v_54 = v_53.widen();
    let mut v_55 = v_49;
    W::U32::add_assign(&mut v_55, &v_54);
    let v_56 = W::Field::from_raw_repr_with_reduction(v_55);
    let mut v_57 = v_43;
    W::Field::mul_assign(&mut v_57, &v_56);
    let v_58 = v_22.widen();
    let v_59 = v_58.shl(16u32);
    let v_60 = v_21.widen();
    let mut v_61 = v_59;
    W::U32::add_assign(&mut v_61, &v_60);
    let v_62 = W::Field::from_raw_repr_with_reduction(v_61);
    let mut v_63 = v_57;
    W::Field::add_assign(&mut v_63, &v_62);
    let v_64 = W::Field::select(&v_11, &v_63, &v_57);
    let v_65 = v_64.into_raw_repr_reduced();
    let v_66 = W::U32::constant(2013265921u32);
    let v_67 = W::U32::overflowing_sub(&v_65, &v_66).1;
    let v_68 = W::Field::from_integer(v_42);
    let v_69 = W::Field::from_integer(v_55);
    let mut v_70 = v_68;
    W::Field::sub_assign(&mut v_70, &v_69);
    let v_71 = v_70.as_integer();
    let v_72 = W::U32::overflowing_sub(&v_71, &v_66).1;
    let mut v_73 = v_68;
    W::Field::add_assign(&mut v_73, &v_69);
    let v_74 = v_73.as_integer();
    let v_75 = W::U32::overflowing_sub(&v_74, &v_66).1;
    let v_76 = v_2.widen();
    let v_77 = v_76.shl(16u32);
    let v_78 = v_1.widen();
    let mut v_79 = v_77;
    W::U32::add_assign(&mut v_79, &v_78);
    let v_80 = v_4.widen();
    let v_81 = v_80.shl(16u32);
    let v_82 = v_3.widen();
    let mut v_83 = v_81;
    W::U32::add_assign(&mut v_83, &v_82);
    let v_84 = W::U32::overflowing_add(&v_79, &v_83).1;
    let v_85 = W::U32::overflowing_sub(&v_42, &v_55).1;
    let v_86 = W::U32::overflowing_add(&v_42, &v_55).1;
    let mut v_87 = v_42;
    W::U32::add_assign(&mut v_87, &v_55);
    let v_88 = W::U32::overflowing_add(&v_87, &v_83).1;
    let v_89 = W::Mask::or(&v_86, &v_88);
    let v_90 = W::Mask::select(&v_5, &v_89, &v_29);
    let v_91 = W::Mask::select(&v_6, &v_85, &v_90);
    let v_92 = W::Mask::select(&v_7, &v_84, &v_91);
    let v_93 = W::Mask::select(&v_8, &v_75, &v_92);
    let v_94 = W::Mask::select(&v_9, &v_72, &v_93);
    let v_95 = W::Mask::select(&v_30, &v_67, &v_94);
    let v_96 = W::Mask::select(&v_12, &v_29, &v_95);
    witness_proxy.set_witness_place_boolean(
        21usize,
        W::Mask::select(
            &v_28,
            &v_96,
            &witness_proxy.get_witness_place_boolean(21usize),
        ),
    );
    let v_98 = v_65.truncate();
    let v_99 = W::U16::constant(1u16);
    let v_100 = W::U16::overflowing_sub(&v_98, &v_99).1;
    let v_101 = v_71.truncate();
    let v_102 = W::U16::overflowing_sub(&v_101, &v_99).1;
    let v_103 = v_74.truncate();
    let v_104 = W::U16::overflowing_sub(&v_103, &v_99).1;
    let v_105 = W::U16::overflowing_add(&v_1, &v_3).1;
    let v_106 = W::U16::overflowing_sub(&v_40, &v_53).1;
    let mut v_107 = v_40;
    W::U16::sub_assign(&mut v_107, &v_53);
    let v_108 = W::U16::overflowing_sub(&v_107, &v_3).1;
    let v_109 = W::Mask::or(&v_106, &v_108);
    let v_110 = W::U16::overflowing_add(&v_40, &v_53).1;
    let mut v_111 = v_40;
    W::U16::add_assign(&mut v_111, &v_53);
    let v_112 = W::U16::overflowing_add(&v_111, &v_3).1;
    let v_113 = W::Mask::or(&v_110, &v_112);
    let v_114 = W::Mask::select(&v_5, &v_113, &v_29);
    let v_115 = W::Mask::select(&v_6, &v_109, &v_114);
    let v_116 = W::Mask::select(&v_7, &v_105, &v_115);
    let v_117 = W::Mask::select(&v_8, &v_104, &v_116);
    let v_118 = W::Mask::select(&v_9, &v_102, &v_117);
    let v_119 = W::Mask::select(&v_30, &v_100, &v_118);
    witness_proxy.set_witness_place_boolean(
        22usize,
        W::Mask::select(
            &v_28,
            &v_119,
            &witness_proxy.get_witness_place_boolean(22usize),
        ),
    );
    let mut v_121 = v_65;
    W::U32::sub_assign(&mut v_121, &v_66);
    let mut v_122 = v_71;
    W::U32::sub_assign(&mut v_122, &v_66);
    let mut v_123 = v_74;
    W::U32::sub_assign(&mut v_123, &v_66);
    let v_124 = W::U32::constant(0u32);
    let v_125 = WitnessComputationCore::select(&v_8, &v_123, &v_124);
    let v_126 = WitnessComputationCore::select(&v_9, &v_122, &v_125);
    let v_127 = WitnessComputationCore::select(&v_30, &v_121, &v_126);
    let v_128 = v_127.truncate();
    witness_proxy.set_witness_place_u16(
        43usize,
        W::U16::select(&v_28, &v_128, &witness_proxy.get_witness_place_u16(43usize)),
    );
    let v_130 = v_127.shr(16u32);
    let v_131 = v_130.truncate();
    witness_proxy.set_witness_place_u16(
        44usize,
        W::U16::select(&v_28, &v_131, &witness_proxy.get_witness_place_u16(44usize)),
    );
    let v_133 = W::Field::from_integer(v_65);
    witness_proxy.set_witness_place(45usize, v_133);
}
#[allow(unused_variables)]
fn eval_fn_4<'a, 'b: 'a, W: WitnessTypeSet<BabyBearField>, P: WitnessProxy<BabyBearField, W> + 'b>(
    witness_proxy: &'a mut P,
) where
    W::Field: Copy,
    W::Mask: Copy,
    W::U32: Copy,
    W::U16: Copy,
    W::U8: Copy,
    W::I32: Copy,
{
    let v_0 = witness_proxy.get_memory_place_u16(26usize);
    let v_1 = witness_proxy.get_memory_place_u16(27usize);
    let v_2 = witness_proxy.get_witness_place_u16(2usize);
    let v_3 = witness_proxy.get_witness_place_u16(3usize);
    let v_4 = witness_proxy.get_witness_place_boolean(14usize);
    let v_5 = witness_proxy.get_witness_place_boolean(15usize);
    let v_6 = witness_proxy.get_witness_place_boolean(16usize);
    let v_7 = witness_proxy.get_witness_place_boolean(17usize);
    let v_8 = witness_proxy.get_memory_place_u8(2usize);
    let v_9 = witness_proxy.get_memory_place_u8(3usize);
    let v_10 = witness_proxy.get_memory_place_u8(4usize);
    let v_11 = witness_proxy.get_memory_place_u8(5usize);
    let v_12 = witness_proxy.get_memory_place_u8(9usize);
    let v_13 = witness_proxy.get_memory_place_u8(10usize);
    let v_14 = witness_proxy.get_memory_place_u8(11usize);
    let v_15 = witness_proxy.get_memory_place_u8(12usize);
    let v_16 = W::Mask::or(&v_7, &v_6);
    let v_17 = W::Mask::or(&v_16, &v_4);
    let v_18 = W::Mask::or(&v_17, &v_5);
    let v_19 = W::Mask::or(&v_4, &v_5);
    let v_20 = W::U16::constant(4u16);
    let v_21 = W::U16::overflowing_add(&v_0, &v_20).1;
    let v_22 = v_9.widen();
    let v_23 = v_22.shl(8u32);
    let v_24 = v_8.widen();
    let mut v_25 = v_23;
    W::U16::add_assign(&mut v_25, &v_24);
    let v_26 = v_13.widen();
    let v_27 = v_26.shl(8u32);
    let v_28 = v_12.widen();
    let mut v_29 = v_27;
    W::U16::add_assign(&mut v_29, &v_28);
    let v_30 = W::U16::overflowing_sub(&v_25, &v_29).1;
    let mut v_31 = v_25;
    W::U16::sub_assign(&mut v_31, &v_29);
    let v_32 = W::U16::overflowing_sub(&v_31, &v_2).1;
    let v_33 = W::Mask::or(&v_30, &v_32);
    let v_34 = W::Mask::constant(false);
    let v_35 = W::Mask::select(&v_7, &v_30, &v_34);
    let v_36 = W::Mask::select(&v_6, &v_33, &v_35);
    let v_37 = W::Mask::select(&v_19, &v_21, &v_36);
    witness_proxy.set_witness_place_boolean(
        21usize,
        W::Mask::select(
            &v_18,
            &v_37,
            &witness_proxy.get_witness_place_boolean(21usize),
        ),
    );
    let v_39 = v_1.widen();
    let v_40 = v_39.shl(16u32);
    let v_41 = v_0.widen();
    let mut v_42 = v_40;
    W::U32::add_assign(&mut v_42, &v_41);
    let v_43 = W::U32::constant(4u32);
    let v_44 = W::U32::overflowing_add(&v_42, &v_43).1;
    let v_45 = v_11.widen();
    let v_46 = v_45.shl(8u32);
    let v_47 = v_10.widen();
    let mut v_48 = v_46;
    W::U16::add_assign(&mut v_48, &v_47);
    let v_49 = v_48.widen();
    let v_50 = v_49.shl(16u32);
    let v_51 = v_25.widen();
    let mut v_52 = v_50;
    W::U32::add_assign(&mut v_52, &v_51);
    let v_53 = v_15.widen();
    let v_54 = v_53.shl(8u32);
    let v_55 = v_14.widen();
    let mut v_56 = v_54;
    W::U16::add_assign(&mut v_56, &v_55);
    let v_57 = v_56.widen();
    let v_58 = v_57.shl(16u32);
    let v_59 = v_29.widen();
    let mut v_60 = v_58;
    W::U32::add_assign(&mut v_60, &v_59);
    let v_61 = W::U32::overflowing_sub(&v_52, &v_60).1;
    let mut v_62 = v_52;
    W::U32::sub_assign(&mut v_62, &v_60);
    let v_63 = v_3.widen();
    let v_64 = v_63.shl(16u32);
    let v_65 = v_2.widen();
    let mut v_66 = v_64;
    W::U32::add_assign(&mut v_66, &v_65);
    let v_67 = W::U32::overflowing_sub(&v_62, &v_66).1;
    let v_68 = W::Mask::or(&v_61, &v_67);
    let v_69 = W::Mask::select(&v_7, &v_61, &v_34);
    let v_70 = W::Mask::select(&v_6, &v_68, &v_69);
    let v_71 = W::Mask::select(&v_19, &v_44, &v_70);
    witness_proxy.set_witness_place_boolean(
        22usize,
        W::Mask::select(
            &v_18,
            &v_71,
            &witness_proxy.get_witness_place_boolean(22usize),
        ),
    );
    let mut v_73 = v_42;
    W::U32::add_assign(&mut v_73, &v_43);
    let mut v_74 = v_62;
    W::U32::sub_assign(&mut v_74, &v_66);
    let v_75 = W::U32::constant(0u32);
    let v_76 = WitnessComputationCore::select(&v_7, &v_62, &v_75);
    let v_77 = WitnessComputationCore::select(&v_6, &v_74, &v_76);
    let v_78 = WitnessComputationCore::select(&v_19, &v_73, &v_77);
    let v_79 = v_78.truncate();
    witness_proxy.set_witness_place_u16(
        43usize,
        W::U16::select(&v_18, &v_79, &witness_proxy.get_witness_place_u16(43usize)),
    );
    let v_81 = v_78.shr(16u32);
    let v_82 = v_81.truncate();
    witness_proxy.set_witness_place_u16(
        44usize,
        W::U16::select(&v_18, &v_82, &witness_proxy.get_witness_place_u16(44usize)),
    );
}
#[allow(unused_variables)]
fn eval_fn_5<'a, 'b: 'a, W: WitnessTypeSet<BabyBearField>, P: WitnessProxy<BabyBearField, W> + 'b>(
    witness_proxy: &'a mut P,
) where
    W::Field: Copy,
    W::Mask: Copy,
    W::U32: Copy,
    W::U16: Copy,
    W::U8: Copy,
    W::I32: Copy,
{
    let v_0 = witness_proxy.get_witness_place(14usize);
    let v_1 = witness_proxy.get_witness_place(15usize);
    let v_2 = witness_proxy.get_witness_place(16usize);
    let v_3 = witness_proxy.get_witness_place(17usize);
    let v_4 = witness_proxy.get_memory_place(4usize);
    let v_5 = witness_proxy.get_memory_place(5usize);
    let v_6 = witness_proxy.get_witness_place_boolean(14usize);
    let v_7 = witness_proxy.get_witness_place_boolean(15usize);
    let v_8 = W::Mask::or(&v_6, &v_7);
    let v_9 = witness_proxy.get_witness_place_boolean(16usize);
    let v_10 = W::Mask::or(&v_8, &v_9);
    let v_11 = witness_proxy.get_witness_place_boolean(17usize);
    let v_12 = W::Mask::or(&v_10, &v_11);
    let v_13 = W::Field::constant(BabyBearField(0u32));
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_0, &v_4);
    let mut v_15 = v_14;
    W::Field::add_assign_product(&mut v_15, &v_1, &v_4);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_2, &v_4);
    let mut v_17 = v_16;
    W::Field::add_assign_product(&mut v_17, &v_3, &v_4);
    let v_18 = W::Field::constant(BabyBearField(268434910u32));
    let mut v_19 = v_0;
    W::Field::mul_assign(&mut v_19, &v_18);
    let mut v_20 = v_17;
    W::Field::add_assign_product(&mut v_20, &v_19, &v_5);
    let mut v_21 = v_1;
    W::Field::mul_assign(&mut v_21, &v_18);
    let mut v_22 = v_20;
    W::Field::add_assign_product(&mut v_22, &v_21, &v_5);
    let mut v_23 = v_2;
    W::Field::mul_assign(&mut v_23, &v_18);
    let mut v_24 = v_22;
    W::Field::add_assign_product(&mut v_24, &v_23, &v_5);
    let mut v_25 = v_3;
    W::Field::mul_assign(&mut v_25, &v_18);
    let mut v_26 = v_24;
    W::Field::add_assign_product(&mut v_26, &v_25, &v_5);
    let v_27 = W::Field::constant(BabyBearField(1342177270u32));
    let mut v_28 = v_13;
    W::Field::add_assign_product(&mut v_28, &v_27, &v_0);
    let mut v_29 = v_28;
    W::Field::add_assign_product(&mut v_29, &v_27, &v_1);
    let mut v_30 = v_29;
    W::Field::add_assign_product(&mut v_30, &v_27, &v_2);
    let mut v_31 = v_30;
    W::Field::add_assign_product(&mut v_31, &v_27, &v_3);
    let v_32 = v_31.as_integer();
    let v_33 = v_32.truncate();
    let v_34 = W::Mask::constant(true);
    let v_35 = witness_proxy.maybe_lookup::<1usize, 1usize>(&[v_26], v_33, v_34);
    let v_36 = v_35[0usize];
    witness_proxy.set_witness_place(
        27usize,
        W::Field::select(&v_12, &v_36, &witness_proxy.get_witness_place(27usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_6<'a, 'b: 'a, W: WitnessTypeSet<BabyBearField>, P: WitnessProxy<BabyBearField, W> + 'b>(
    witness_proxy: &'a mut P,
) where
    W::Field: Copy,
    W::Mask: Copy,
    W::U32: Copy,
    W::U16: Copy,
    W::U8: Copy,
    W::I32: Copy,
{
    let v_0 = witness_proxy.get_witness_place_boolean(14usize);
    let v_1 = witness_proxy.get_witness_place_boolean(15usize);
    let v_2 = witness_proxy.get_witness_place_boolean(16usize);
    let v_3 = witness_proxy.get_witness_place_boolean(17usize);
    let v_4 = witness_proxy.get_witness_place_boolean(18usize);
    let v_5 = W::Mask::or(&v_0, &v_1);
    let v_6 = W::Mask::negate(&v_4);
    let v_7 = W::Mask::and(&v_5, &v_6);
    witness_proxy.set_witness_place_boolean(48usize, v_7);
    let v_9 = W::Mask::and(&v_2, &v_6);
    witness_proxy.set_witness_place_boolean(49usize, v_9);
    let v_11 = W::Mask::or(&v_5, &v_2);
    let v_12 = W::Mask::or(&v_11, &v_3);
    let v_13 = W::Mask::and(&v_12, &v_4);
    witness_proxy.set_witness_place_boolean(50usize, v_13);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_7<'a, 'b: 'a, W: WitnessTypeSet<BabyBearField>, P: WitnessProxy<BabyBearField, W> + 'b>(
    witness_proxy: &'a mut P,
) where
    W::Field: Copy,
    W::Mask: Copy,
    W::U32: Copy,
    W::U16: Copy,
    W::U8: Copy,
    W::I32: Copy,
{
    let v_0 = witness_proxy.get_witness_place(3usize);
    let v_1 = witness_proxy.get_witness_place_boolean(20usize);
    let v_2 = W::Field::constant(BabyBearField(805306362u32));
    let v_3 = v_2.as_integer();
    let v_4 = v_3.truncate();
    let v_5 = witness_proxy.maybe_lookup::<1usize, 1usize>(&[v_0], v_4, v_1);
    let v_6 = v_5[0usize];
    witness_proxy.set_witness_place(
        26usize,
        W::Field::select(&v_1, &v_6, &witness_proxy.get_witness_place(26usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_8<'a, 'b: 'a, W: WitnessTypeSet<BabyBearField>, P: WitnessProxy<BabyBearField, W> + 'b>(
    witness_proxy: &'a mut P,
) where
    W::Field: Copy,
    W::Mask: Copy,
    W::U32: Copy,
    W::U16: Copy,
    W::U8: Copy,
    W::I32: Copy,
{
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(20usize);
    let v_3 = witness_proxy.get_memory_place(2usize);
    let v_4 = witness_proxy.get_memory_place(9usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let v_6 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_7 = v_5;
    W::Field::add_assign_product(&mut v_7, &v_6, &v_0);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_6, &v_4);
    let v_9 = v_1.as_integer();
    let v_10 = v_9.truncate();
    let v_11 = witness_proxy.maybe_lookup::<2usize, 1usize>(&[v_3, v_8], v_10, v_2);
    let v_12 = v_11[0usize];
    witness_proxy.set_witness_place(
        27usize,
        W::Field::select(&v_2, &v_12, &witness_proxy.get_witness_place(27usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_9<'a, 'b: 'a, W: WitnessTypeSet<BabyBearField>, P: WitnessProxy<BabyBearField, W> + 'b>(
    witness_proxy: &'a mut P,
) where
    W::Field: Copy,
    W::Mask: Copy,
    W::U32: Copy,
    W::U16: Copy,
    W::U8: Copy,
    W::I32: Copy,
{
    let v_0 = witness_proxy.get_witness_place(3usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(20usize);
    let v_3 = witness_proxy.get_memory_place(3usize);
    let v_4 = witness_proxy.get_memory_place(10usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let v_6 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_7 = v_5;
    W::Field::add_assign_product(&mut v_7, &v_6, &v_0);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_6, &v_4);
    let v_9 = v_1.as_integer();
    let v_10 = v_9.truncate();
    let v_11 = witness_proxy.maybe_lookup::<2usize, 1usize>(&[v_3, v_8], v_10, v_2);
    let v_12 = v_11[0usize];
    witness_proxy.set_witness_place(
        28usize,
        W::Field::select(&v_2, &v_12, &witness_proxy.get_witness_place(28usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_10<
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
    let v_0 = witness_proxy.get_witness_place_boolean(19usize);
    let v_1 = witness_proxy.get_memory_place(9usize);
    let v_2 = witness_proxy.get_memory_place(10usize);
    let v_3 = W::Field::constant(BabyBearField(134217711u32));
    let v_4 = v_3.as_integer();
    let v_5 = v_4.truncate();
    let v_6 = witness_proxy.maybe_lookup::<2usize, 1usize>(&[v_1, v_2], v_5, v_0);
    let v_7 = v_6[0usize];
    witness_proxy.set_witness_place(
        26usize,
        W::Field::select(&v_0, &v_7, &witness_proxy.get_witness_place(26usize)),
    );
}
#[allow(unused_variables)]
fn eval_fn_11<
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
    let v_0 = witness_proxy.get_witness_place_u16(2usize);
    let v_1 = witness_proxy.get_witness_place_u16(3usize);
    let v_2 = witness_proxy.get_memory_place_boolean(13usize);
    let v_3 = witness_proxy.get_memory_place_boolean(20usize);
    let v_4 = witness_proxy.get_memory_place_u8(2usize);
    let v_5 = witness_proxy.get_memory_place_u8(3usize);
    let v_6 = witness_proxy.get_memory_place_u8(4usize);
    let v_7 = witness_proxy.get_memory_place_u8(5usize);
    let v_8 = W::Mask::or(&v_2, &v_3);
    let v_9 = v_5.widen();
    let v_10 = v_9.shl(8u32);
    let v_11 = v_4.widen();
    let mut v_12 = v_10;
    W::U16::add_assign(&mut v_12, &v_11);
    let v_13 = W::U16::overflowing_add(&v_12, &v_0).1;
    witness_proxy.set_witness_place_boolean(
        21usize,
        W::Mask::select(
            &v_8,
            &v_13,
            &witness_proxy.get_witness_place_boolean(21usize),
        ),
    );
    let v_15 = v_7.widen();
    let v_16 = v_15.shl(8u32);
    let v_17 = v_6.widen();
    let mut v_18 = v_16;
    W::U16::add_assign(&mut v_18, &v_17);
    let v_19 = W::U16::overflowing_add(&v_18, &v_1).1;
    let mut v_20 = v_18;
    W::U16::add_assign(&mut v_20, &v_1);
    let v_21 = W::U32::from_mask(v_13);
    let v_22 = v_21.truncate();
    let v_23 = W::U16::overflowing_add(&v_20, &v_22).1;
    let v_24 = W::Mask::or(&v_19, &v_23);
    witness_proxy.set_witness_place_boolean(
        22usize,
        W::Mask::select(
            &v_8,
            &v_24,
            &witness_proxy.get_witness_place_boolean(22usize),
        ),
    );
}
#[allow(unused_variables)]
fn eval_fn_12<
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
    let v_0 = witness_proxy.get_memory_place(13usize);
    let v_1 = witness_proxy.get_memory_place(20usize);
    let v_2 = witness_proxy.get_memory_place(14usize);
    let v_3 = witness_proxy.get_memory_place(15usize);
    let v_4 = witness_proxy.get_memory_place(21usize);
    let v_5 = witness_proxy.get_memory_place(22usize);
    let v_6 = witness_proxy.get_memory_place_boolean(13usize);
    let v_7 = witness_proxy.get_memory_place_boolean(20usize);
    let v_8 = W::Mask::or(&v_6, &v_7);
    let v_9 = W::Field::constant(BabyBearField(0u32));
    let mut v_10 = v_9;
    W::Field::add_assign_product(&mut v_10, &v_0, &v_2);
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_1, &v_4);
    witness_proxy.set_witness_place(
        26usize,
        W::Field::select(&v_8, &v_11, &witness_proxy.get_witness_place(26usize)),
    );
    let mut v_13 = v_9;
    W::Field::add_assign_product(&mut v_13, &v_0, &v_3);
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_1, &v_5);
    witness_proxy.set_witness_place(
        27usize,
        W::Field::select(&v_8, &v_14, &witness_proxy.get_witness_place(27usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_13<
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
    let v_0 = witness_proxy.get_memory_place(13usize);
    let v_1 = witness_proxy.get_memory_place(20usize);
    let v_2 = witness_proxy.get_memory_place(15usize);
    let v_3 = witness_proxy.get_memory_place(22usize);
    let v_4 = witness_proxy.get_memory_place_boolean(13usize);
    let v_5 = witness_proxy.get_memory_place_boolean(20usize);
    let v_6 = W::Mask::or(&v_4, &v_5);
    let v_7 = W::Field::constant(BabyBearField(0u32));
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_0, &v_2);
    let mut v_9 = v_8;
    W::Field::add_assign_product(&mut v_9, &v_1, &v_3);
    let v_10 = v_9.as_integer();
    let v_11 = v_10.shr(6u32);
    let v_12 = W::U32::constant(0u32);
    let v_13 = W::U32::equal(&v_11, &v_12);
    witness_proxy.set_witness_place_boolean(
        23usize,
        W::Mask::select(
            &v_6,
            &v_13,
            &witness_proxy.get_witness_place_boolean(23usize),
        ),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_14<
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
    let v_0 = witness_proxy.get_memory_place_boolean(20usize);
    let v_1 = witness_proxy.get_memory_place_u16(21usize);
    let v_2 = v_1.get_lowest_bits(1u32);
    let v_3 = W::U16::constant(1u16);
    let v_4 = W::U16::equal(&v_2, &v_3);
    witness_proxy.set_witness_place_boolean(
        24usize,
        W::Mask::select(
            &v_0,
            &v_4,
            &witness_proxy.get_witness_place_boolean(24usize),
        ),
    );
    let v_6 = v_1.shr(1u32);
    let v_7 = v_6.get_lowest_bits(1u32);
    let v_8 = W::U16::equal(&v_7, &v_3);
    witness_proxy.set_witness_place_boolean(
        25usize,
        W::Mask::select(
            &v_0,
            &v_8,
            &witness_proxy.get_witness_place_boolean(25usize),
        ),
    );
    let v_10 = v_1.shr(2u32);
    witness_proxy.set_witness_place_u16(
        43usize,
        W::U16::select(&v_0, &v_10, &witness_proxy.get_witness_place_u16(43usize)),
    );
}
#[allow(unused_variables)]
fn eval_fn_15<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_witness_place(19usize);
    let v_6 = witness_proxy.get_witness_place(20usize);
    let v_7 = W::Field::constant(BabyBearField(0u32));
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_0, &v_6);
    let v_9 = W::Field::constant(BabyBearField(1342177270u32));
    let mut v_10 = v_8;
    W::Field::add_assign_product(&mut v_10, &v_9, &v_1);
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_9, &v_2);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_9, &v_3);
    let mut v_13 = v_12;
    W::Field::add_assign_product(&mut v_13, &v_9, &v_4);
    let v_14 = W::Field::constant(BabyBearField(402653165u32));
    let mut v_15 = v_13;
    W::Field::add_assign_product(&mut v_15, &v_14, &v_5);
    witness_proxy.set_scratch_place(5usize, v_15);
}
#[allow(unused_variables)]
fn eval_fn_16<
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
    let v_0 = witness_proxy.get_witness_place(14usize);
    let v_1 = witness_proxy.get_witness_place(15usize);
    let v_2 = witness_proxy.get_witness_place(16usize);
    let v_3 = witness_proxy.get_witness_place(17usize);
    let v_4 = witness_proxy.get_witness_place(20usize);
    let v_5 = witness_proxy.get_memory_place(2usize);
    let v_6 = witness_proxy.get_memory_place(4usize);
    let v_7 = witness_proxy.get_memory_place(5usize);
    let v_8 = W::Field::constant(BabyBearField(0u32));
    let mut v_9 = v_8;
    W::Field::add_assign_product(&mut v_9, &v_0, &v_6);
    let mut v_10 = v_9;
    W::Field::add_assign_product(&mut v_10, &v_1, &v_6);
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_2, &v_6);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_3, &v_6);
    let mut v_13 = v_12;
    W::Field::add_assign_product(&mut v_13, &v_4, &v_5);
    let v_14 = W::Field::constant(BabyBearField(268434910u32));
    let mut v_15 = v_0;
    W::Field::mul_assign(&mut v_15, &v_14);
    let mut v_16 = v_13;
    W::Field::add_assign_product(&mut v_16, &v_15, &v_7);
    let mut v_17 = v_1;
    W::Field::mul_assign(&mut v_17, &v_14);
    let mut v_18 = v_16;
    W::Field::add_assign_product(&mut v_18, &v_17, &v_7);
    let mut v_19 = v_2;
    W::Field::mul_assign(&mut v_19, &v_14);
    let mut v_20 = v_18;
    W::Field::add_assign_product(&mut v_20, &v_19, &v_7);
    let mut v_21 = v_3;
    W::Field::mul_assign(&mut v_21, &v_14);
    let mut v_22 = v_20;
    W::Field::add_assign_product(&mut v_22, &v_21, &v_7);
    witness_proxy.set_scratch_place(6usize, v_22);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_17<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(9usize, v_3);
}
#[allow(unused_variables)]
fn eval_fn_18<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_witness_place(19usize);
    let v_6 = witness_proxy.get_witness_place(20usize);
    let v_7 = W::Field::constant(BabyBearField(0u32));
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_0, &v_6);
    let v_9 = W::Field::constant(BabyBearField(268435390u32));
    let mut v_10 = v_8;
    W::Field::add_assign_product(&mut v_10, &v_9, &v_1);
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_9, &v_2);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_9, &v_3);
    let mut v_13 = v_12;
    W::Field::add_assign_product(&mut v_13, &v_9, &v_4);
    let v_14 = W::Field::constant(BabyBearField(402653165u32));
    let mut v_15 = v_13;
    W::Field::add_assign_product(&mut v_15, &v_14, &v_5);
    witness_proxy.set_scratch_place(14usize, v_15);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_19<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(18usize, v_3);
}
#[allow(unused_variables)]
fn eval_fn_20<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_witness_place(19usize);
    let v_6 = witness_proxy.get_witness_place(20usize);
    let v_7 = W::Field::constant(BabyBearField(0u32));
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_0, &v_6);
    let v_9 = W::Field::constant(BabyBearField(536870908u32));
    let mut v_10 = v_8;
    W::Field::add_assign_product(&mut v_10, &v_9, &v_1);
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_9, &v_2);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_9, &v_3);
    let mut v_13 = v_12;
    W::Field::add_assign_product(&mut v_13, &v_9, &v_4);
    let v_14 = W::Field::constant(BabyBearField(402653165u32));
    let mut v_15 = v_13;
    W::Field::add_assign_product(&mut v_15, &v_14, &v_5);
    witness_proxy.set_scratch_place(23usize, v_15);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_21<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(27usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_22<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_witness_place(20usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_0, &v_2);
    let v_5 = W::Field::constant(BabyBearField(402653165u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_1);
    witness_proxy.set_scratch_place(32usize, v_6);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_23<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(20usize);
    let v_2 = witness_proxy.get_memory_place(5usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_1, &v_2);
    let v_5 = W::Field::constant(BabyBearField(805306362u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_0);
    witness_proxy.set_scratch_place(33usize, v_6);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_24<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(36usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_25<
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
    let v_0 = witness_proxy.get_memory_place_u16(26usize);
    let v_1 = W::U16::constant(4u16);
    let v_2 = W::U16::overflowing_add(&v_0, &v_1).1;
    witness_proxy.set_witness_place_boolean(52usize, v_2);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_26<
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
    let v_0 = witness_proxy.get_memory_place_boolean(25usize);
    let v_1 = witness_proxy.get_witness_place_boolean(14usize);
    let v_2 = witness_proxy.get_witness_place_boolean(15usize);
    let v_3 = witness_proxy.get_witness_place_boolean(16usize);
    let v_4 = witness_proxy.get_witness_place_boolean(17usize);
    let v_5 = W::Mask::or(&v_1, &v_2);
    let v_6 = W::Mask::or(&v_5, &v_3);
    let v_7 = W::Mask::or(&v_6, &v_4);
    let v_8 = W::Mask::negate(&v_7);
    let v_9 = W::Mask::and(&v_0, &v_8);
    witness_proxy.set_witness_place_boolean(53usize, v_9);
}
#[allow(unused_variables)]
fn eval_fn_27<
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
    let v_0 = witness_proxy.get_memory_place_boolean(25usize);
    let v_1 = witness_proxy.get_witness_place_boolean(5usize);
    let v_2 = witness_proxy.get_witness_place_boolean(6usize);
    let v_3 = witness_proxy.get_witness_place_boolean(7usize);
    let v_4 = witness_proxy.get_witness_place_boolean(8usize);
    let v_5 = witness_proxy.get_witness_place_boolean(9usize);
    let v_6 = witness_proxy.get_witness_place_boolean(10usize);
    let v_7 = witness_proxy.get_witness_place_boolean(11usize);
    let v_8 = witness_proxy.get_witness_place_boolean(12usize);
    let v_9 = witness_proxy.get_witness_place_boolean(13usize);
    let v_10 = witness_proxy.get_witness_place_boolean(14usize);
    let v_11 = witness_proxy.get_witness_place_boolean(15usize);
    let v_12 = witness_proxy.get_witness_place_boolean(16usize);
    let v_13 = witness_proxy.get_witness_place_boolean(17usize);
    let v_14 = witness_proxy.get_witness_place_boolean(19usize);
    let v_15 = witness_proxy.get_witness_place_boolean(20usize);
    let v_16 = witness_proxy.get_memory_place_boolean(13usize);
    let v_17 = witness_proxy.get_memory_place_boolean(20usize);
    let v_18 = W::Mask::or(&v_1, &v_2);
    let v_19 = W::Mask::or(&v_18, &v_3);
    let v_20 = W::Mask::or(&v_19, &v_4);
    let v_21 = W::Mask::or(&v_20, &v_5);
    let v_22 = W::Mask::or(&v_21, &v_6);
    let v_23 = W::Mask::or(&v_22, &v_7);
    let v_24 = W::Mask::or(&v_23, &v_8);
    let v_25 = W::Mask::or(&v_24, &v_9);
    let v_26 = W::Mask::or(&v_25, &v_10);
    let v_27 = W::Mask::or(&v_26, &v_11);
    let v_28 = W::Mask::or(&v_27, &v_12);
    let v_29 = W::Mask::or(&v_28, &v_13);
    let v_30 = W::Mask::or(&v_29, &v_14);
    let v_31 = W::Mask::or(&v_30, &v_15);
    let v_32 = W::Mask::or(&v_31, &v_16);
    let v_33 = W::Mask::or(&v_32, &v_17);
    let v_34 = W::Mask::and(&v_0, &v_33);
    witness_proxy.set_witness_place_boolean(54usize, v_34);
}
#[allow(unused_variables)]
fn eval_fn_28<
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
    let v_0 = witness_proxy.get_witness_place(14usize);
    let v_1 = witness_proxy.get_witness_place(15usize);
    let v_2 = witness_proxy.get_witness_place(16usize);
    let v_3 = witness_proxy.get_witness_place(17usize);
    let v_4 = witness_proxy.get_witness_place(43usize);
    let v_5 = witness_proxy.get_witness_place(44usize);
    let v_6 = witness_proxy.get_witness_place_boolean(14usize);
    let v_7 = witness_proxy.get_witness_place_boolean(15usize);
    let v_8 = W::Mask::or(&v_6, &v_7);
    let v_9 = witness_proxy.get_witness_place_boolean(16usize);
    let v_10 = W::Mask::or(&v_8, &v_9);
    let v_11 = witness_proxy.get_witness_place_boolean(17usize);
    let v_12 = W::Mask::or(&v_10, &v_11);
    let v_13 = W::Field::constant(BabyBearField(0u32));
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_0, &v_4);
    let mut v_15 = v_14;
    W::Field::add_assign_product(&mut v_15, &v_0, &v_5);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_1, &v_4);
    let mut v_17 = v_16;
    W::Field::add_assign_product(&mut v_17, &v_1, &v_5);
    let mut v_18 = v_17;
    W::Field::add_assign_product(&mut v_18, &v_2, &v_4);
    let mut v_19 = v_18;
    W::Field::add_assign_product(&mut v_19, &v_2, &v_5);
    let mut v_20 = v_19;
    W::Field::add_assign_product(&mut v_20, &v_3, &v_4);
    let mut v_21 = v_20;
    W::Field::add_assign_product(&mut v_21, &v_3, &v_5);
    let mut v_22 = v_13;
    W::Field::add_assign(&mut v_22, &v_0);
    let mut v_23 = v_22;
    W::Field::add_assign(&mut v_23, &v_1);
    let mut v_24 = v_23;
    W::Field::add_assign(&mut v_24, &v_2);
    let mut v_25 = v_24;
    W::Field::add_assign(&mut v_25, &v_3);
    let v_26 = v_25.as_integer();
    let v_27 = v_26.truncate();
    let v_28 = W::Mask::constant(true);
    let v_29 = witness_proxy.maybe_lookup::<1usize, 1usize>(&[v_21], v_27, v_28);
    let v_30 = v_29[0usize];
    witness_proxy.set_witness_place(
        26usize,
        W::Field::select(&v_12, &v_30, &witness_proxy.get_witness_place(26usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_29<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place_boolean(20usize);
    let v_2 = witness_proxy.get_memory_place(4usize);
    let v_3 = witness_proxy.get_memory_place(11usize);
    let v_4 = witness_proxy.get_witness_place(26usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let v_6 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_7 = v_5;
    W::Field::add_assign_product(&mut v_7, &v_6, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_6, &v_4);
    let v_9 = v_0.as_integer();
    let v_10 = v_9.truncate();
    let v_11 = witness_proxy.maybe_lookup::<2usize, 1usize>(&[v_2, v_8], v_10, v_1);
    let v_12 = v_11[0usize];
    witness_proxy.set_witness_place(
        29usize,
        W::Field::select(&v_1, &v_12, &witness_proxy.get_witness_place(29usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_30<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place_boolean(20usize);
    let v_2 = witness_proxy.get_memory_place(5usize);
    let v_3 = witness_proxy.get_memory_place(12usize);
    let v_4 = witness_proxy.get_witness_place(26usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let v_6 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_7 = v_5;
    W::Field::add_assign_product(&mut v_7, &v_6, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_6, &v_4);
    let v_9 = v_0.as_integer();
    let v_10 = v_9.truncate();
    let v_11 = witness_proxy.maybe_lookup::<2usize, 1usize>(&[v_2, v_8], v_10, v_1);
    let v_12 = v_11[0usize];
    witness_proxy.set_witness_place(
        30usize,
        W::Field::select(&v_1, &v_12, &witness_proxy.get_witness_place(30usize)),
    );
}
#[allow(unused_variables)]
fn eval_fn_31<
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(19usize);
    let v_3 = witness_proxy.get_memory_place(2usize);
    let v_4 = witness_proxy.get_witness_place(26usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let v_6 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_7 = v_5;
    W::Field::add_assign_product(&mut v_7, &v_6, &v_0);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_6, &v_4);
    let v_9 = W::Field::constant(BabyBearField(402653165u32));
    let v_10 = v_9.as_integer();
    let v_11 = v_10.truncate();
    let v_12 = witness_proxy.maybe_lookup::<4usize, 4usize>(&[v_5, v_3, v_8, v_1], v_11, v_2);
    let v_13 = v_12[0usize];
    witness_proxy.set_witness_place(
        27usize,
        W::Field::select(&v_2, &v_13, &witness_proxy.get_witness_place(27usize)),
    );
    let v_15 = v_12[1usize];
    witness_proxy.set_witness_place(
        28usize,
        W::Field::select(&v_2, &v_15, &witness_proxy.get_witness_place(28usize)),
    );
    let v_17 = v_12[2usize];
    witness_proxy.set_witness_place(
        29usize,
        W::Field::select(&v_2, &v_17, &witness_proxy.get_witness_place(29usize)),
    );
    let v_19 = v_12[3usize];
    witness_proxy.set_witness_place(
        30usize,
        W::Field::select(&v_2, &v_19, &witness_proxy.get_witness_place(30usize)),
    );
}
#[allow(unused_variables)]
fn eval_fn_32<
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(19usize);
    let v_3 = witness_proxy.get_memory_place(3usize);
    let v_4 = witness_proxy.get_witness_place(26usize);
    let v_5 = W::Field::constant(BabyBearField(268435454u32));
    let v_6 = W::Field::constant(BabyBearField(0u32));
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_5, &v_0);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_5, &v_4);
    let v_9 = W::Field::constant(BabyBearField(402653165u32));
    let v_10 = v_9.as_integer();
    let v_11 = v_10.truncate();
    let v_12 = witness_proxy.maybe_lookup::<4usize, 4usize>(&[v_5, v_3, v_8, v_1], v_11, v_2);
    let v_13 = v_12[0usize];
    witness_proxy.set_witness_place(
        31usize,
        W::Field::select(&v_2, &v_13, &witness_proxy.get_witness_place(31usize)),
    );
    let v_15 = v_12[1usize];
    witness_proxy.set_witness_place(
        32usize,
        W::Field::select(&v_2, &v_15, &witness_proxy.get_witness_place(32usize)),
    );
    let v_17 = v_12[2usize];
    witness_proxy.set_witness_place(
        33usize,
        W::Field::select(&v_2, &v_17, &witness_proxy.get_witness_place(33usize)),
    );
    let v_19 = v_12[3usize];
    witness_proxy.set_witness_place(
        34usize,
        W::Field::select(&v_2, &v_19, &witness_proxy.get_witness_place(34usize)),
    );
}
#[allow(unused_variables)]
fn eval_fn_33<
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(19usize);
    let v_3 = witness_proxy.get_memory_place(4usize);
    let v_4 = witness_proxy.get_witness_place(26usize);
    let v_5 = W::Field::constant(BabyBearField(536870908u32));
    let v_6 = W::Field::constant(BabyBearField(0u32));
    let v_7 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_8 = v_6;
    W::Field::add_assign_product(&mut v_8, &v_7, &v_0);
    let mut v_9 = v_8;
    W::Field::add_assign_product(&mut v_9, &v_7, &v_4);
    let v_10 = W::Field::constant(BabyBearField(402653165u32));
    let v_11 = v_10.as_integer();
    let v_12 = v_11.truncate();
    let v_13 = witness_proxy.maybe_lookup::<4usize, 4usize>(&[v_5, v_3, v_9, v_1], v_12, v_2);
    let v_14 = v_13[0usize];
    witness_proxy.set_witness_place(
        35usize,
        W::Field::select(&v_2, &v_14, &witness_proxy.get_witness_place(35usize)),
    );
    let v_16 = v_13[1usize];
    witness_proxy.set_witness_place(
        36usize,
        W::Field::select(&v_2, &v_16, &witness_proxy.get_witness_place(36usize)),
    );
    let v_18 = v_13[2usize];
    witness_proxy.set_witness_place(
        37usize,
        W::Field::select(&v_2, &v_18, &witness_proxy.get_witness_place(37usize)),
    );
    let v_20 = v_13[3usize];
    witness_proxy.set_witness_place(
        38usize,
        W::Field::select(&v_2, &v_20, &witness_proxy.get_witness_place(38usize)),
    );
}
#[allow(unused_variables)]
fn eval_fn_34<
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(19usize);
    let v_3 = witness_proxy.get_memory_place(5usize);
    let v_4 = witness_proxy.get_witness_place(26usize);
    let v_5 = W::Field::constant(BabyBearField(805306362u32));
    let v_6 = W::Field::constant(BabyBearField(0u32));
    let v_7 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_8 = v_6;
    W::Field::add_assign_product(&mut v_8, &v_7, &v_0);
    let mut v_9 = v_8;
    W::Field::add_assign_product(&mut v_9, &v_7, &v_4);
    let v_10 = W::Field::constant(BabyBearField(402653165u32));
    let v_11 = v_10.as_integer();
    let v_12 = v_11.truncate();
    let v_13 = witness_proxy.maybe_lookup::<4usize, 4usize>(&[v_5, v_3, v_9, v_1], v_12, v_2);
    let v_14 = v_13[0usize];
    witness_proxy.set_witness_place(
        39usize,
        W::Field::select(&v_2, &v_14, &witness_proxy.get_witness_place(39usize)),
    );
    let v_16 = v_13[1usize];
    witness_proxy.set_witness_place(
        40usize,
        W::Field::select(&v_2, &v_16, &witness_proxy.get_witness_place(40usize)),
    );
    let v_18 = v_13[2usize];
    witness_proxy.set_witness_place(
        41usize,
        W::Field::select(&v_2, &v_18, &witness_proxy.get_witness_place(41usize)),
    );
    let v_20 = v_13[3usize];
    witness_proxy.set_witness_place(
        42usize,
        W::Field::select(&v_2, &v_20, &witness_proxy.get_witness_place(42usize)),
    );
}
#[allow(unused_variables)]
fn eval_fn_35<
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_witness_place(19usize);
    let v_6 = witness_proxy.get_witness_place(20usize);
    let v_7 = witness_proxy.get_memory_place(2usize);
    let v_8 = witness_proxy.get_memory_place(9usize);
    let v_9 = witness_proxy.get_witness_place(27usize);
    let v_10 = W::Field::constant(BabyBearField(0u32));
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_0, &v_6);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_1, &v_9);
    let mut v_13 = v_12;
    W::Field::add_assign_product(&mut v_13, &v_2, &v_9);
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_3, &v_9);
    let mut v_15 = v_14;
    W::Field::add_assign_product(&mut v_15, &v_4, &v_9);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_5, &v_7);
    let mut v_17 = v_16;
    W::Field::add_assign_product(&mut v_17, &v_6, &v_8);
    witness_proxy.set_scratch_place(7usize, v_17);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_36<
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_witness_place(20usize);
    let v_3 = witness_proxy.get_witness_place(26usize);
    let v_4 = witness_proxy.get_witness_place(27usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_1);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_2, &v_4);
    witness_proxy.set_scratch_place(8usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_37<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(27usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(10usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_38<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(29usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(12usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_39<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(30usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(13usize, v_3);
}
#[allow(unused_variables)]
fn eval_fn_40<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_witness_place(19usize);
    let v_6 = witness_proxy.get_witness_place(20usize);
    let v_7 = witness_proxy.get_memory_place(3usize);
    let v_8 = witness_proxy.get_memory_place(11usize);
    let v_9 = witness_proxy.get_memory_place(12usize);
    let v_10 = witness_proxy.get_witness_place(22usize);
    let v_11 = witness_proxy.get_witness_place(26usize);
    let v_12 = witness_proxy.get_witness_place(27usize);
    let v_13 = W::Field::constant(BabyBearField(0u32));
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_1, &v_8);
    let mut v_15 = v_14;
    W::Field::add_assign_product(&mut v_15, &v_2, &v_8);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_3, &v_8);
    let mut v_17 = v_16;
    W::Field::add_assign_product(&mut v_17, &v_4, &v_8);
    let mut v_18 = v_17;
    W::Field::add_assign_product(&mut v_18, &v_6, &v_7);
    let v_19 = W::Field::constant(BabyBearField(133099247u32));
    let mut v_20 = v_0;
    W::Field::mul_assign(&mut v_20, &v_19);
    let mut v_21 = v_18;
    W::Field::add_assign_product(&mut v_21, &v_20, &v_1);
    let mut v_22 = v_21;
    W::Field::add_assign_product(&mut v_22, &v_20, &v_2);
    let mut v_23 = v_22;
    W::Field::add_assign_product(&mut v_23, &v_20, &v_3);
    let mut v_24 = v_23;
    W::Field::add_assign_product(&mut v_24, &v_20, &v_4);
    let v_25 = W::Field::constant(BabyBearField(268434910u32));
    let mut v_26 = v_1;
    W::Field::mul_assign(&mut v_26, &v_25);
    let mut v_27 = v_24;
    W::Field::add_assign_product(&mut v_27, &v_26, &v_9);
    let v_28 = W::Field::constant(BabyBearField(536591292u32));
    let mut v_29 = v_1;
    W::Field::mul_assign(&mut v_29, &v_28);
    let mut v_30 = v_27;
    W::Field::add_assign_product(&mut v_30, &v_29, &v_10);
    let v_31 = W::Field::constant(BabyBearField(1073182584u32));
    let mut v_32 = v_1;
    W::Field::mul_assign(&mut v_32, &v_31);
    let mut v_33 = v_30;
    W::Field::add_assign_product(&mut v_33, &v_32, &v_11);
    let v_34 = W::Field::constant(BabyBearField(268295646u32));
    let mut v_35 = v_1;
    W::Field::mul_assign(&mut v_35, &v_34);
    let mut v_36 = v_33;
    W::Field::add_assign_product(&mut v_36, &v_35, &v_12);
    let mut v_37 = v_2;
    W::Field::mul_assign(&mut v_37, &v_25);
    let mut v_38 = v_36;
    W::Field::add_assign_product(&mut v_38, &v_37, &v_9);
    let mut v_39 = v_2;
    W::Field::mul_assign(&mut v_39, &v_28);
    let mut v_40 = v_38;
    W::Field::add_assign_product(&mut v_40, &v_39, &v_10);
    let mut v_41 = v_2;
    W::Field::mul_assign(&mut v_41, &v_31);
    let mut v_42 = v_40;
    W::Field::add_assign_product(&mut v_42, &v_41, &v_11);
    let mut v_43 = v_2;
    W::Field::mul_assign(&mut v_43, &v_34);
    let mut v_44 = v_42;
    W::Field::add_assign_product(&mut v_44, &v_43, &v_12);
    let mut v_45 = v_3;
    W::Field::mul_assign(&mut v_45, &v_25);
    let mut v_46 = v_44;
    W::Field::add_assign_product(&mut v_46, &v_45, &v_9);
    let mut v_47 = v_3;
    W::Field::mul_assign(&mut v_47, &v_28);
    let mut v_48 = v_46;
    W::Field::add_assign_product(&mut v_48, &v_47, &v_10);
    let mut v_49 = v_3;
    W::Field::mul_assign(&mut v_49, &v_31);
    let mut v_50 = v_48;
    W::Field::add_assign_product(&mut v_50, &v_49, &v_11);
    let mut v_51 = v_3;
    W::Field::mul_assign(&mut v_51, &v_34);
    let mut v_52 = v_50;
    W::Field::add_assign_product(&mut v_52, &v_51, &v_12);
    let mut v_53 = v_4;
    W::Field::mul_assign(&mut v_53, &v_25);
    let mut v_54 = v_52;
    W::Field::add_assign_product(&mut v_54, &v_53, &v_9);
    let mut v_55 = v_4;
    W::Field::mul_assign(&mut v_55, &v_28);
    let mut v_56 = v_54;
    W::Field::add_assign_product(&mut v_56, &v_55, &v_10);
    let mut v_57 = v_4;
    W::Field::mul_assign(&mut v_57, &v_31);
    let mut v_58 = v_56;
    W::Field::add_assign_product(&mut v_58, &v_57, &v_11);
    let mut v_59 = v_4;
    W::Field::mul_assign(&mut v_59, &v_34);
    let mut v_60 = v_58;
    W::Field::add_assign_product(&mut v_60, &v_59, &v_12);
    let mut v_61 = v_60;
    W::Field::add_assign(&mut v_61, &v_5);
    witness_proxy.set_scratch_place(15usize, v_61);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_41<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(31usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(19usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_42<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(32usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(20usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_43<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(33usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(21usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_44<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(34usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(22usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_45<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(35usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(28usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_46<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(36usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(29usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_47<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(37usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(30usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_48<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(38usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(31usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_49<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(20usize);
    let v_2 = witness_proxy.get_memory_place(5usize);
    let v_3 = witness_proxy.get_memory_place(12usize);
    let v_4 = witness_proxy.get_witness_place(26usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_2);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_1, &v_4);
    witness_proxy.set_scratch_place(34usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_50<
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_witness_place(20usize);
    let v_3 = witness_proxy.get_witness_place(26usize);
    let v_4 = witness_proxy.get_witness_place(30usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_1);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_2, &v_4);
    witness_proxy.set_scratch_place(35usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_51<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(39usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(37usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_52<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(40usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(38usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_53<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(41usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(39usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_54<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(42usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(40usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_55<
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
    let v_0 = witness_proxy.get_scratch_place_u16(32usize);
    let v_1 = witness_proxy.get_scratch_place(33usize);
    let v_2 = witness_proxy.get_scratch_place(34usize);
    let v_3 = witness_proxy.get_scratch_place(35usize);
    let v_4 = witness_proxy.get_scratch_place(36usize);
    let v_5 = witness_proxy.get_scratch_place(37usize);
    let v_6 = witness_proxy.get_scratch_place(38usize);
    let v_7 = witness_proxy.get_scratch_place(39usize);
    let v_8 = witness_proxy.get_scratch_place(40usize);
    let v_9 = witness_proxy.lookup_enforce::<8usize>(
        &[v_1, v_2, v_3, v_4, v_5, v_6, v_7, v_8],
        v_0,
        4usize,
    );
}
#[allow(unused_variables)]
fn eval_fn_56<
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_memory_place(11usize);
    let v_6 = witness_proxy.get_memory_place(12usize);
    let v_7 = witness_proxy.get_witness_place(22usize);
    let v_8 = witness_proxy.get_witness_place(26usize);
    let v_9 = witness_proxy.get_witness_place(27usize);
    let v_10 = witness_proxy.get_witness_place_boolean(14usize);
    let v_11 = witness_proxy.get_witness_place_boolean(15usize);
    let v_12 = W::Mask::or(&v_10, &v_11);
    let v_13 = witness_proxy.get_witness_place_boolean(16usize);
    let v_14 = W::Mask::or(&v_12, &v_13);
    let v_15 = witness_proxy.get_witness_place_boolean(17usize);
    let v_16 = W::Mask::or(&v_14, &v_15);
    let v_17 = W::Field::constant(BabyBearField(0u32));
    let mut v_18 = v_17;
    W::Field::add_assign_product(&mut v_18, &v_1, &v_5);
    let mut v_19 = v_18;
    W::Field::add_assign_product(&mut v_19, &v_2, &v_5);
    let mut v_20 = v_19;
    W::Field::add_assign_product(&mut v_20, &v_3, &v_5);
    let mut v_21 = v_20;
    W::Field::add_assign_product(&mut v_21, &v_4, &v_5);
    let v_22 = W::Field::constant(BabyBearField(133099247u32));
    let mut v_23 = v_0;
    W::Field::mul_assign(&mut v_23, &v_22);
    let mut v_24 = v_21;
    W::Field::add_assign_product(&mut v_24, &v_23, &v_1);
    let mut v_25 = v_24;
    W::Field::add_assign_product(&mut v_25, &v_23, &v_2);
    let mut v_26 = v_25;
    W::Field::add_assign_product(&mut v_26, &v_23, &v_3);
    let mut v_27 = v_26;
    W::Field::add_assign_product(&mut v_27, &v_23, &v_4);
    let v_28 = W::Field::constant(BabyBearField(268434910u32));
    let mut v_29 = v_1;
    W::Field::mul_assign(&mut v_29, &v_28);
    let mut v_30 = v_27;
    W::Field::add_assign_product(&mut v_30, &v_29, &v_6);
    let v_31 = W::Field::constant(BabyBearField(536591292u32));
    let mut v_32 = v_1;
    W::Field::mul_assign(&mut v_32, &v_31);
    let mut v_33 = v_30;
    W::Field::add_assign_product(&mut v_33, &v_32, &v_7);
    let v_34 = W::Field::constant(BabyBearField(1073182584u32));
    let mut v_35 = v_1;
    W::Field::mul_assign(&mut v_35, &v_34);
    let mut v_36 = v_33;
    W::Field::add_assign_product(&mut v_36, &v_35, &v_8);
    let v_37 = W::Field::constant(BabyBearField(268295646u32));
    let mut v_38 = v_1;
    W::Field::mul_assign(&mut v_38, &v_37);
    let mut v_39 = v_36;
    W::Field::add_assign_product(&mut v_39, &v_38, &v_9);
    let mut v_40 = v_2;
    W::Field::mul_assign(&mut v_40, &v_28);
    let mut v_41 = v_39;
    W::Field::add_assign_product(&mut v_41, &v_40, &v_6);
    let mut v_42 = v_2;
    W::Field::mul_assign(&mut v_42, &v_31);
    let mut v_43 = v_41;
    W::Field::add_assign_product(&mut v_43, &v_42, &v_7);
    let mut v_44 = v_2;
    W::Field::mul_assign(&mut v_44, &v_34);
    let mut v_45 = v_43;
    W::Field::add_assign_product(&mut v_45, &v_44, &v_8);
    let mut v_46 = v_2;
    W::Field::mul_assign(&mut v_46, &v_37);
    let mut v_47 = v_45;
    W::Field::add_assign_product(&mut v_47, &v_46, &v_9);
    let mut v_48 = v_3;
    W::Field::mul_assign(&mut v_48, &v_28);
    let mut v_49 = v_47;
    W::Field::add_assign_product(&mut v_49, &v_48, &v_6);
    let mut v_50 = v_3;
    W::Field::mul_assign(&mut v_50, &v_31);
    let mut v_51 = v_49;
    W::Field::add_assign_product(&mut v_51, &v_50, &v_7);
    let mut v_52 = v_3;
    W::Field::mul_assign(&mut v_52, &v_34);
    let mut v_53 = v_51;
    W::Field::add_assign_product(&mut v_53, &v_52, &v_8);
    let mut v_54 = v_3;
    W::Field::mul_assign(&mut v_54, &v_37);
    let mut v_55 = v_53;
    W::Field::add_assign_product(&mut v_55, &v_54, &v_9);
    let mut v_56 = v_4;
    W::Field::mul_assign(&mut v_56, &v_28);
    let mut v_57 = v_55;
    W::Field::add_assign_product(&mut v_57, &v_56, &v_6);
    let mut v_58 = v_4;
    W::Field::mul_assign(&mut v_58, &v_31);
    let mut v_59 = v_57;
    W::Field::add_assign_product(&mut v_59, &v_58, &v_7);
    let mut v_60 = v_4;
    W::Field::mul_assign(&mut v_60, &v_34);
    let mut v_61 = v_59;
    W::Field::add_assign_product(&mut v_61, &v_60, &v_8);
    let mut v_62 = v_4;
    W::Field::mul_assign(&mut v_62, &v_37);
    let mut v_63 = v_61;
    W::Field::add_assign_product(&mut v_63, &v_62, &v_9);
    let v_64 = W::Field::constant(BabyBearField(268435390u32));
    let mut v_65 = v_17;
    W::Field::add_assign_product(&mut v_65, &v_64, &v_1);
    let mut v_66 = v_65;
    W::Field::add_assign_product(&mut v_66, &v_64, &v_2);
    let mut v_67 = v_66;
    W::Field::add_assign_product(&mut v_67, &v_64, &v_3);
    let mut v_68 = v_67;
    W::Field::add_assign_product(&mut v_68, &v_64, &v_4);
    let v_69 = v_68.as_integer();
    let v_70 = v_69.truncate();
    let v_71 = W::Mask::constant(true);
    let v_72 = witness_proxy.maybe_lookup::<1usize, 1usize>(&[v_63], v_70, v_71);
    let v_73 = v_72[0usize];
    witness_proxy.set_witness_place(
        28usize,
        W::Field::select(&v_16, &v_73, &witness_proxy.get_witness_place(28usize)),
    );
}
#[allow(unused_variables)]
fn eval_fn_57<
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
    let v_0 = witness_proxy.get_memory_place_u16(26usize);
    let v_1 = witness_proxy.get_memory_place_u16(27usize);
    let v_2 = witness_proxy.get_witness_place_u16(2usize);
    let v_3 = witness_proxy.get_witness_place_u16(3usize);
    let v_4 = witness_proxy.get_witness_place_boolean(14usize);
    let v_5 = witness_proxy.get_witness_place_boolean(15usize);
    let v_6 = witness_proxy.get_witness_place_boolean(16usize);
    let v_7 = witness_proxy.get_witness_place_boolean(17usize);
    let v_8 = witness_proxy.get_memory_place_u8(2usize);
    let v_9 = witness_proxy.get_memory_place_u8(3usize);
    let v_10 = witness_proxy.get_memory_place_u8(4usize);
    let v_11 = witness_proxy.get_memory_place_u8(5usize);
    let v_12 = witness_proxy.get_witness_place_boolean(28usize);
    let v_13 = v_1.widen();
    let v_14 = v_13.shl(16u32);
    let v_15 = v_0.widen();
    let mut v_16 = v_14;
    W::U32::add_assign(&mut v_16, &v_15);
    let v_17 = W::U32::constant(4u32);
    let mut v_18 = v_16;
    W::U32::add_assign(&mut v_18, &v_17);
    let v_19 = v_11.widen();
    let v_20 = v_19.shl(8u32);
    let v_21 = v_10.widen();
    let mut v_22 = v_20;
    W::U16::add_assign(&mut v_22, &v_21);
    let v_23 = v_22.widen();
    let v_24 = v_23.shl(16u32);
    let v_25 = v_9.widen();
    let v_26 = v_25.shl(8u32);
    let v_27 = v_8.widen();
    let mut v_28 = v_26;
    W::U16::add_assign(&mut v_28, &v_27);
    let v_29 = v_28.widen();
    let mut v_30 = v_24;
    W::U32::add_assign(&mut v_30, &v_29);
    let v_31 = v_3.widen();
    let v_32 = v_31.shl(16u32);
    let v_33 = v_2.widen();
    let mut v_34 = v_32;
    W::U32::add_assign(&mut v_34, &v_33);
    let mut v_35 = v_30;
    W::U32::add_assign(&mut v_35, &v_34);
    let mut v_36 = v_16;
    W::U32::add_assign(&mut v_36, &v_34);
    let v_37 = W::Mask::and(&v_7, &v_12);
    let v_38 = WitnessComputationCore::select(&v_37, &v_36, &v_18);
    let v_39 = WitnessComputationCore::select(&v_4, &v_36, &v_38);
    let v_40 = WitnessComputationCore::select(&v_5, &v_35, &v_39);
    let v_41 = WitnessComputationCore::select(&v_6, &v_18, &v_40);
    let v_42 = v_41.shr(16u32);
    let v_43 = v_42.truncate();
    let v_45 = W::Mask::or(&v_7, &v_6);
    let v_46 = W::Mask::or(&v_45, &v_4);
    let v_47 = W::Mask::or(&v_46, &v_5);
    let v_48 = W::U16::constant(4u16);
    let v_49 = W::U16::overflowing_add(&v_0, &v_48).1;
    let v_50 = W::U16::overflowing_add(&v_28, &v_2).1;
    let v_51 = W::U16::overflowing_add(&v_0, &v_2).1;
    let v_52 = W::U32::overflowing_add(&v_16, &v_17).1;
    let v_53 = W::Mask::select(&v_37, &v_51, &v_52);
    let v_54 = W::Mask::select(&v_4, &v_51, &v_53);
    let v_55 = W::Mask::select(&v_5, &v_50, &v_54);
    let v_56 = W::Mask::select(&v_6, &v_49, &v_55);
    witness_proxy.set_witness_place_boolean(
        23usize,
        W::Mask::select(
            &v_47,
            &v_56,
            &witness_proxy.get_witness_place_boolean(23usize),
        ),
    );
    let v_58 = W::U32::overflowing_add(&v_30, &v_34).1;
    let v_59 = W::U32::overflowing_add(&v_16, &v_34).1;
    let v_60 = W::Mask::select(&v_37, &v_59, &v_49);
    let v_61 = W::Mask::select(&v_4, &v_59, &v_60);
    let v_62 = W::Mask::select(&v_5, &v_58, &v_61);
    let v_63 = W::Mask::select(&v_6, &v_52, &v_62);
    witness_proxy.set_witness_place_boolean(
        24usize,
        W::Mask::select(
            &v_47,
            &v_63,
            &witness_proxy.get_witness_place_boolean(24usize),
        ),
    );
    let v_65 = v_41.truncate();
    witness_proxy.set_witness_place_u16(46usize, v_65);
    witness_proxy.set_witness_place_boolean(47usize, v_37);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_58<
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
    let v_0 = witness_proxy.get_witness_place_boolean(14usize);
    let v_1 = witness_proxy.get_witness_place_boolean(15usize);
    let v_2 = witness_proxy.get_witness_place_boolean(16usize);
    let v_3 = witness_proxy.get_witness_place_boolean(17usize);
    let v_4 = witness_proxy.get_witness_place_u16(46usize);
    let v_5 = W::Mask::or(&v_3, &v_2);
    let v_6 = W::Mask::or(&v_5, &v_0);
    let v_7 = W::Mask::or(&v_6, &v_1);
    let v_8 = v_4.shr(1u32);
    let v_9 = v_8.get_lowest_bits(1u32);
    let v_10 = W::U16::constant(1u16);
    let v_11 = W::U16::equal(&v_9, &v_10);
    witness_proxy.set_witness_place_boolean(
        25usize,
        W::Mask::select(
            &v_7,
            &v_11,
            &witness_proxy.get_witness_place_boolean(25usize),
        ),
    );
}
#[allow(unused_variables)]
fn eval_fn_60<
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
    let v_0 = witness_proxy.get_memory_place(13usize);
    let v_1 = witness_proxy.get_memory_place(20usize);
    let v_2 = witness_proxy.get_witness_place(23usize);
    let v_3 = witness_proxy.get_witness_place(27usize);
    let v_4 = W::Field::constant(BabyBearField(0u32));
    let mut v_5 = v_4;
    W::Field::add_assign_product(&mut v_5, &v_0, &v_3);
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_1, &v_3);
    let v_7 = W::Field::constant(BabyBearField(268295646u32));
    let mut v_8 = v_0;
    W::Field::mul_assign(&mut v_8, &v_7);
    let mut v_9 = v_6;
    W::Field::add_assign_product(&mut v_9, &v_8, &v_2);
    let mut v_10 = v_1;
    W::Field::mul_assign(&mut v_10, &v_7);
    let mut v_11 = v_9;
    W::Field::add_assign_product(&mut v_11, &v_10, &v_2);
    let v_12 = W::Field::constant(BabyBearField(939524233u32));
    let mut v_13 = v_11;
    W::Field::add_assign_product(&mut v_13, &v_12, &v_0);
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_12, &v_1);
    witness_proxy.set_scratch_place(0usize, v_14);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_61<
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
    let v_0 = witness_proxy.get_memory_place_boolean(13usize);
    let v_1 = witness_proxy.get_memory_place_boolean(20usize);
    let v_2 = witness_proxy.get_witness_place_boolean(23usize);
    let v_3 = W::Mask::or(&v_0, &v_1);
    let v_4 = W::Mask::and(&v_3, &v_2);
    witness_proxy.set_witness_place_boolean(51usize, v_4);
}
#[allow(unused_variables)]
fn eval_fn_62<
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
    let v_0 = witness_proxy.get_memory_place(25usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_witness_place(19usize);
    let v_6 = witness_proxy.get_witness_place(20usize);
    let v_7 = witness_proxy.get_witness_place(51usize);
    let v_8 = W::Field::constant(BabyBearField(0u32));
    let v_9 = W::Field::constant(BabyBearField(1073741752u32));
    let mut v_10 = v_0;
    W::Field::mul_assign(&mut v_10, &v_9);
    let mut v_11 = v_8;
    W::Field::add_assign_product(&mut v_11, &v_10, &v_7);
    let mut v_12 = v_11;
    W::Field::add_assign(&mut v_12, &v_1);
    let mut v_13 = v_12;
    W::Field::add_assign(&mut v_13, &v_2);
    let mut v_14 = v_13;
    W::Field::add_assign(&mut v_14, &v_3);
    let mut v_15 = v_14;
    W::Field::add_assign(&mut v_15, &v_4);
    let v_16 = W::Field::constant(BabyBearField(134217711u32));
    let mut v_17 = v_15;
    W::Field::add_assign_product(&mut v_17, &v_16, &v_5);
    let v_18 = W::Field::constant(BabyBearField(805306362u32));
    let mut v_19 = v_17;
    W::Field::add_assign_product(&mut v_19, &v_18, &v_6);
    witness_proxy.set_scratch_place(1usize, v_19);
}
#[allow(unused_variables)]
fn eval_fn_63<
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
    let v_0 = witness_proxy.get_witness_place(3usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_witness_place(19usize);
    let v_6 = witness_proxy.get_witness_place(20usize);
    let v_7 = witness_proxy.get_memory_place(9usize);
    let v_8 = witness_proxy.get_witness_place(26usize);
    let v_9 = witness_proxy.get_witness_place(27usize);
    let v_10 = witness_proxy.get_witness_place(43usize);
    let v_11 = witness_proxy.get_witness_place(44usize);
    let v_12 = witness_proxy.get_witness_place(51usize);
    let v_13 = W::Field::constant(BabyBearField(0u32));
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_0, &v_6);
    let mut v_15 = v_14;
    W::Field::add_assign_product(&mut v_15, &v_1, &v_10);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_1, &v_11);
    let mut v_17 = v_16;
    W::Field::add_assign_product(&mut v_17, &v_2, &v_10);
    let mut v_18 = v_17;
    W::Field::add_assign_product(&mut v_18, &v_2, &v_11);
    let mut v_19 = v_18;
    W::Field::add_assign_product(&mut v_19, &v_3, &v_10);
    let mut v_20 = v_19;
    W::Field::add_assign_product(&mut v_20, &v_3, &v_11);
    let mut v_21 = v_20;
    W::Field::add_assign_product(&mut v_21, &v_4, &v_10);
    let mut v_22 = v_21;
    W::Field::add_assign_product(&mut v_22, &v_4, &v_11);
    let mut v_23 = v_22;
    W::Field::add_assign_product(&mut v_23, &v_5, &v_7);
    let mut v_24 = v_23;
    W::Field::add_assign_product(&mut v_24, &v_8, &v_12);
    let v_25 = W::Field::constant(BabyBearField(268295646u32));
    let mut v_26 = v_9;
    W::Field::mul_assign(&mut v_26, &v_25);
    let mut v_27 = v_24;
    W::Field::add_assign_product(&mut v_27, &v_26, &v_12);
    witness_proxy.set_scratch_place(2usize, v_27);
}
#[allow(unused_variables)]
fn eval_fn_64<
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
    let v_0 = witness_proxy.get_witness_place(14usize);
    let v_1 = witness_proxy.get_witness_place(15usize);
    let v_2 = witness_proxy.get_witness_place(16usize);
    let v_3 = witness_proxy.get_witness_place(17usize);
    let v_4 = witness_proxy.get_witness_place(19usize);
    let v_5 = witness_proxy.get_witness_place(20usize);
    let v_6 = witness_proxy.get_memory_place(13usize);
    let v_7 = witness_proxy.get_memory_place(20usize);
    let v_8 = witness_proxy.get_memory_place(9usize);
    let v_9 = witness_proxy.get_memory_place(10usize);
    let v_10 = witness_proxy.get_memory_place(23usize);
    let v_11 = witness_proxy.get_witness_place(26usize);
    let v_12 = witness_proxy.get_witness_place(51usize);
    let v_13 = W::Field::constant(BabyBearField(0u32));
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_0, &v_11);
    let mut v_15 = v_14;
    W::Field::add_assign_product(&mut v_15, &v_1, &v_11);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_2, &v_11);
    let mut v_17 = v_16;
    W::Field::add_assign_product(&mut v_17, &v_3, &v_11);
    let mut v_18 = v_17;
    W::Field::add_assign_product(&mut v_18, &v_4, &v_9);
    let mut v_19 = v_18;
    W::Field::add_assign_product(&mut v_19, &v_5, &v_11);
    let mut v_20 = v_19;
    W::Field::add_assign_product(&mut v_20, &v_6, &v_10);
    let mut v_21 = v_20;
    W::Field::add_assign_product(&mut v_21, &v_7, &v_10);
    let mut v_22 = v_21;
    W::Field::add_assign_product(&mut v_22, &v_8, &v_12);
    let mut v_23 = v_6;
    W::Field::mul_assign(&mut v_23, &v_8);
    let mut v_24 = v_22;
    W::Field::sub_assign(&mut v_24, &v_23);
    let mut v_25 = v_7;
    W::Field::mul_assign(&mut v_25, &v_8);
    let mut v_26 = v_24;
    W::Field::sub_assign(&mut v_26, &v_25);
    let v_27 = W::Field::constant(BabyBearField(1744831011u32));
    let mut v_28 = v_6;
    W::Field::mul_assign(&mut v_28, &v_27);
    let mut v_29 = v_26;
    W::Field::add_assign_product(&mut v_29, &v_28, &v_9);
    let mut v_30 = v_7;
    W::Field::mul_assign(&mut v_30, &v_27);
    let mut v_31 = v_29;
    W::Field::add_assign_product(&mut v_31, &v_30, &v_9);
    let v_32 = W::Field::constant(BabyBearField(268434910u32));
    let mut v_33 = v_9;
    W::Field::mul_assign(&mut v_33, &v_32);
    let mut v_34 = v_31;
    W::Field::add_assign_product(&mut v_34, &v_33, &v_12);
    witness_proxy.set_scratch_place(3usize, v_34);
}
#[allow(unused_variables)]
fn eval_fn_65<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_memory_place(13usize);
    let v_2 = witness_proxy.get_memory_place(20usize);
    let v_3 = witness_proxy.get_memory_place(11usize);
    let v_4 = witness_proxy.get_memory_place(12usize);
    let v_5 = witness_proxy.get_memory_place(24usize);
    let v_6 = witness_proxy.get_witness_place(26usize);
    let v_7 = witness_proxy.get_witness_place(51usize);
    let v_8 = W::Field::constant(BabyBearField(0u32));
    let mut v_9 = v_8;
    W::Field::add_assign_product(&mut v_9, &v_0, &v_6);
    let mut v_10 = v_9;
    W::Field::add_assign_product(&mut v_10, &v_1, &v_5);
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_2, &v_5);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_3, &v_7);
    let mut v_13 = v_1;
    W::Field::mul_assign(&mut v_13, &v_3);
    let mut v_14 = v_12;
    W::Field::sub_assign(&mut v_14, &v_13);
    let mut v_15 = v_2;
    W::Field::mul_assign(&mut v_15, &v_3);
    let mut v_16 = v_14;
    W::Field::sub_assign(&mut v_16, &v_15);
    let v_17 = W::Field::constant(BabyBearField(1744831011u32));
    let mut v_18 = v_1;
    W::Field::mul_assign(&mut v_18, &v_17);
    let mut v_19 = v_16;
    W::Field::add_assign_product(&mut v_19, &v_18, &v_4);
    let mut v_20 = v_2;
    W::Field::mul_assign(&mut v_20, &v_17);
    let mut v_21 = v_19;
    W::Field::add_assign_product(&mut v_21, &v_20, &v_4);
    let v_22 = W::Field::constant(BabyBearField(268434910u32));
    let mut v_23 = v_4;
    W::Field::mul_assign(&mut v_23, &v_22);
    let mut v_24 = v_21;
    W::Field::add_assign_product(&mut v_24, &v_23, &v_7);
    witness_proxy.set_scratch_place(4usize, v_24);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_66<
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
    let v_0 = witness_proxy.get_scratch_place_u16(1usize);
    let v_1 = witness_proxy.get_scratch_place(2usize);
    let v_2 = witness_proxy.get_scratch_place(3usize);
    let v_3 = witness_proxy.get_scratch_place(4usize);
    let v_4 = W::Field::constant(BabyBearField(0u32));
    let v_5 = witness_proxy.lookup_enforce::<8usize>(
        &[v_1, v_2, v_3, v_4, v_4, v_4, v_4, v_4],
        v_0,
        0usize,
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_67<
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(28usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(11usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_68<
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
    let v_0 = witness_proxy.get_scratch_place_u16(5usize);
    let v_1 = witness_proxy.get_scratch_place(6usize);
    let v_2 = witness_proxy.get_scratch_place(7usize);
    let v_3 = witness_proxy.get_scratch_place(8usize);
    let v_4 = witness_proxy.get_scratch_place(9usize);
    let v_5 = witness_proxy.get_scratch_place(10usize);
    let v_6 = witness_proxy.get_scratch_place(11usize);
    let v_7 = witness_proxy.get_scratch_place(12usize);
    let v_8 = witness_proxy.get_scratch_place(13usize);
    let v_9 = witness_proxy.lookup_enforce::<8usize>(
        &[v_1, v_2, v_3, v_4, v_5, v_6, v_7, v_8],
        v_0,
        1usize,
    );
}
#[allow(unused_variables)]
fn eval_fn_69<
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
    let v_0 = witness_proxy.get_witness_place(3usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_witness_place(19usize);
    let v_6 = witness_proxy.get_witness_place(20usize);
    let v_7 = witness_proxy.get_memory_place(3usize);
    let v_8 = witness_proxy.get_memory_place(10usize);
    let v_9 = witness_proxy.get_witness_place(28usize);
    let v_10 = W::Field::constant(BabyBearField(0u32));
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_0, &v_6);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_1, &v_9);
    let mut v_13 = v_12;
    W::Field::add_assign_product(&mut v_13, &v_2, &v_9);
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_3, &v_9);
    let mut v_15 = v_14;
    W::Field::add_assign_product(&mut v_15, &v_4, &v_9);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_5, &v_7);
    let mut v_17 = v_16;
    W::Field::add_assign_product(&mut v_17, &v_6, &v_8);
    witness_proxy.set_scratch_place(16usize, v_17);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_70<
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_witness_place(20usize);
    let v_3 = witness_proxy.get_witness_place(26usize);
    let v_4 = witness_proxy.get_witness_place(28usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_1);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_2, &v_4);
    witness_proxy.set_scratch_place(17usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_71<
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
    let v_0 = witness_proxy.get_scratch_place_u16(14usize);
    let v_1 = witness_proxy.get_scratch_place(15usize);
    let v_2 = witness_proxy.get_scratch_place(16usize);
    let v_3 = witness_proxy.get_scratch_place(17usize);
    let v_4 = witness_proxy.get_scratch_place(18usize);
    let v_5 = witness_proxy.get_scratch_place(19usize);
    let v_6 = witness_proxy.get_scratch_place(20usize);
    let v_7 = witness_proxy.get_scratch_place(21usize);
    let v_8 = witness_proxy.get_scratch_place(22usize);
    let v_9 = witness_proxy.lookup_enforce::<8usize>(
        &[v_1, v_2, v_3, v_4, v_5, v_6, v_7, v_8],
        v_0,
        2usize,
    );
}
#[allow(unused_variables)]
fn eval_fn_72<
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
    let v_0 = witness_proxy.get_witness_place(14usize);
    let v_1 = witness_proxy.get_witness_place(15usize);
    let v_2 = witness_proxy.get_witness_place(16usize);
    let v_3 = witness_proxy.get_witness_place(17usize);
    let v_4 = witness_proxy.get_witness_place(19usize);
    let v_5 = witness_proxy.get_witness_place(20usize);
    let v_6 = witness_proxy.get_memory_place(4usize);
    let v_7 = witness_proxy.get_witness_place(46usize);
    let v_8 = W::Field::constant(BabyBearField(0u32));
    let mut v_9 = v_8;
    W::Field::add_assign_product(&mut v_9, &v_0, &v_7);
    let mut v_10 = v_9;
    W::Field::add_assign_product(&mut v_10, &v_1, &v_7);
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_2, &v_7);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_3, &v_7);
    let mut v_13 = v_12;
    W::Field::add_assign_product(&mut v_13, &v_5, &v_6);
    let v_14 = W::Field::constant(BabyBearField(536870908u32));
    let mut v_15 = v_13;
    W::Field::add_assign_product(&mut v_15, &v_14, &v_4);
    witness_proxy.set_scratch_place(24usize, v_15);
}
#[allow(unused_variables)]
fn eval_fn_73<
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
    let v_0 = witness_proxy.get_witness_place(14usize);
    let v_1 = witness_proxy.get_witness_place(15usize);
    let v_2 = witness_proxy.get_witness_place(16usize);
    let v_3 = witness_proxy.get_witness_place(17usize);
    let v_4 = witness_proxy.get_witness_place(19usize);
    let v_5 = witness_proxy.get_witness_place(20usize);
    let v_6 = witness_proxy.get_memory_place(4usize);
    let v_7 = witness_proxy.get_memory_place(11usize);
    let v_8 = witness_proxy.get_witness_place(25usize);
    let v_9 = witness_proxy.get_witness_place(26usize);
    let v_10 = W::Field::constant(BabyBearField(0u32));
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_0, &v_8);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_1, &v_8);
    let mut v_13 = v_12;
    W::Field::add_assign_product(&mut v_13, &v_2, &v_8);
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_3, &v_8);
    let mut v_15 = v_14;
    W::Field::add_assign_product(&mut v_15, &v_4, &v_6);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_5, &v_7);
    let mut v_17 = v_16;
    W::Field::add_assign_product(&mut v_17, &v_5, &v_9);
    witness_proxy.set_scratch_place(25usize, v_17);
}
#[allow(unused_variables)]
fn eval_fn_74<
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(14usize);
    let v_2 = witness_proxy.get_witness_place(15usize);
    let v_3 = witness_proxy.get_witness_place(16usize);
    let v_4 = witness_proxy.get_witness_place(17usize);
    let v_5 = witness_proxy.get_witness_place(19usize);
    let v_6 = witness_proxy.get_witness_place(20usize);
    let v_7 = witness_proxy.get_memory_place(30usize);
    let v_8 = witness_proxy.get_witness_place(26usize);
    let v_9 = witness_proxy.get_witness_place(29usize);
    let v_10 = W::Field::constant(BabyBearField(0u32));
    let mut v_11 = v_10;
    W::Field::add_assign_product(&mut v_11, &v_0, &v_5);
    let mut v_12 = v_11;
    W::Field::add_assign_product(&mut v_12, &v_1, &v_7);
    let mut v_13 = v_12;
    W::Field::add_assign_product(&mut v_13, &v_2, &v_7);
    let mut v_14 = v_13;
    W::Field::add_assign_product(&mut v_14, &v_3, &v_7);
    let mut v_15 = v_14;
    W::Field::add_assign_product(&mut v_15, &v_4, &v_7);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_5, &v_8);
    let mut v_17 = v_16;
    W::Field::add_assign_product(&mut v_17, &v_6, &v_9);
    witness_proxy.set_scratch_place(26usize, v_17);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_75<
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
    let v_0 = witness_proxy.get_scratch_place_u16(23usize);
    let v_1 = witness_proxy.get_scratch_place(24usize);
    let v_2 = witness_proxy.get_scratch_place(25usize);
    let v_3 = witness_proxy.get_scratch_place(26usize);
    let v_4 = witness_proxy.get_scratch_place(27usize);
    let v_5 = witness_proxy.get_scratch_place(28usize);
    let v_6 = witness_proxy.get_scratch_place(29usize);
    let v_7 = witness_proxy.get_scratch_place(30usize);
    let v_8 = witness_proxy.get_scratch_place(31usize);
    let v_9 = witness_proxy.lookup_enforce::<8usize>(
        &[v_1, v_2, v_3, v_4, v_5, v_6, v_7, v_8],
        v_0,
        3usize,
    );
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
    eval_fn_3(witness_proxy);
    eval_fn_4(witness_proxy);
    eval_fn_5(witness_proxy);
    eval_fn_6(witness_proxy);
    eval_fn_7(witness_proxy);
    eval_fn_8(witness_proxy);
    eval_fn_9(witness_proxy);
    eval_fn_10(witness_proxy);
    eval_fn_11(witness_proxy);
    eval_fn_12(witness_proxy);
    eval_fn_13(witness_proxy);
    eval_fn_14(witness_proxy);
    eval_fn_15(witness_proxy);
    eval_fn_16(witness_proxy);
    eval_fn_17(witness_proxy);
    eval_fn_18(witness_proxy);
    eval_fn_19(witness_proxy);
    eval_fn_20(witness_proxy);
    eval_fn_21(witness_proxy);
    eval_fn_22(witness_proxy);
    eval_fn_23(witness_proxy);
    eval_fn_24(witness_proxy);
    eval_fn_25(witness_proxy);
    eval_fn_26(witness_proxy);
    eval_fn_27(witness_proxy);
    eval_fn_28(witness_proxy);
    eval_fn_29(witness_proxy);
    eval_fn_30(witness_proxy);
    eval_fn_31(witness_proxy);
    eval_fn_32(witness_proxy);
    eval_fn_33(witness_proxy);
    eval_fn_34(witness_proxy);
    eval_fn_35(witness_proxy);
    eval_fn_36(witness_proxy);
    eval_fn_37(witness_proxy);
    eval_fn_38(witness_proxy);
    eval_fn_39(witness_proxy);
    eval_fn_40(witness_proxy);
    eval_fn_41(witness_proxy);
    eval_fn_42(witness_proxy);
    eval_fn_43(witness_proxy);
    eval_fn_44(witness_proxy);
    eval_fn_45(witness_proxy);
    eval_fn_46(witness_proxy);
    eval_fn_47(witness_proxy);
    eval_fn_48(witness_proxy);
    eval_fn_49(witness_proxy);
    eval_fn_50(witness_proxy);
    eval_fn_51(witness_proxy);
    eval_fn_52(witness_proxy);
    eval_fn_53(witness_proxy);
    eval_fn_54(witness_proxy);
    eval_fn_55(witness_proxy);
    eval_fn_56(witness_proxy);
    eval_fn_57(witness_proxy);
    eval_fn_58(witness_proxy);
    eval_fn_60(witness_proxy);
    eval_fn_61(witness_proxy);
    eval_fn_62(witness_proxy);
    eval_fn_63(witness_proxy);
    eval_fn_64(witness_proxy);
    eval_fn_65(witness_proxy);
    eval_fn_66(witness_proxy);
    eval_fn_67(witness_proxy);
    eval_fn_68(witness_proxy);
    eval_fn_69(witness_proxy);
    eval_fn_70(witness_proxy);
    eval_fn_71(witness_proxy);
    eval_fn_72(witness_proxy);
    eval_fn_73(witness_proxy);
    eval_fn_74(witness_proxy);
    eval_fn_75(witness_proxy);
}
