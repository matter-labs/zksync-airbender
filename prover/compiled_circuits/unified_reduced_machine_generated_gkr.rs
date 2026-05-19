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
    let v_11 = witness_proxy.get_witness_place_boolean(12usize);
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
    witness_proxy.set_witness_place_u16(20usize, v_60);
    let v_62 = v_59.shr(16u32);
    let v_63 = v_62.truncate();
    witness_proxy.set_witness_place_u16(21usize, v_63);
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
    witness_proxy.set_witness_place_boolean(22usize, v_87);
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
    witness_proxy.set_witness_place_boolean(23usize, v_112);
    witness_proxy.set_witness_place(24usize, v_46);
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
    let v_4 = witness_proxy.get_witness_place_boolean(13usize);
    let v_5 = witness_proxy.get_witness_place_boolean(14usize);
    let v_6 = witness_proxy.get_witness_place_boolean(15usize);
    let v_7 = witness_proxy.get_witness_place_boolean(16usize);
    let v_8 = witness_proxy.get_memory_place_u8(2usize);
    let v_9 = witness_proxy.get_memory_place_u8(3usize);
    let v_10 = witness_proxy.get_memory_place_u8(4usize);
    let v_11 = witness_proxy.get_memory_place_u8(5usize);
    let v_12 = witness_proxy.get_memory_place_u8(9usize);
    let v_13 = witness_proxy.get_memory_place_u8(10usize);
    let v_14 = witness_proxy.get_memory_place_u8(11usize);
    let v_15 = witness_proxy.get_memory_place_u8(12usize);
    let v_16 = W::Mask::or(&v_4, &v_5);
    let v_17 = v_1.widen();
    let v_18 = v_17.shl(16u32);
    let v_19 = v_0.widen();
    let mut v_20 = v_18;
    W::U32::add_assign(&mut v_20, &v_19);
    let v_21 = W::U32::constant(4u32);
    let mut v_22 = v_20;
    W::U32::add_assign(&mut v_22, &v_21);
    let v_23 = v_11.widen();
    let v_24 = v_23.shl(8u32);
    let v_25 = v_10.widen();
    let mut v_26 = v_24;
    W::U16::add_assign(&mut v_26, &v_25);
    let v_27 = v_26.widen();
    let v_28 = v_27.shl(16u32);
    let v_29 = v_9.widen();
    let v_30 = v_29.shl(8u32);
    let v_31 = v_8.widen();
    let mut v_32 = v_30;
    W::U16::add_assign(&mut v_32, &v_31);
    let v_33 = v_32.widen();
    let mut v_34 = v_28;
    W::U32::add_assign(&mut v_34, &v_33);
    let v_35 = v_15.widen();
    let v_36 = v_35.shl(8u32);
    let v_37 = v_14.widen();
    let mut v_38 = v_36;
    W::U16::add_assign(&mut v_38, &v_37);
    let v_39 = v_38.widen();
    let v_40 = v_39.shl(16u32);
    let v_41 = v_13.widen();
    let v_42 = v_41.shl(8u32);
    let v_43 = v_12.widen();
    let mut v_44 = v_42;
    W::U16::add_assign(&mut v_44, &v_43);
    let v_45 = v_44.widen();
    let mut v_46 = v_40;
    W::U32::add_assign(&mut v_46, &v_45);
    let mut v_47 = v_34;
    W::U32::sub_assign(&mut v_47, &v_46);
    let v_48 = v_3.widen();
    let v_49 = v_48.shl(16u32);
    let v_50 = v_2.widen();
    let mut v_51 = v_49;
    W::U32::add_assign(&mut v_51, &v_50);
    let mut v_52 = v_47;
    W::U32::sub_assign(&mut v_52, &v_51);
    let v_53 = W::U32::constant(0u32);
    let v_54 = WitnessComputationCore::select(&v_7, &v_47, &v_53);
    let v_55 = WitnessComputationCore::select(&v_6, &v_52, &v_54);
    let v_56 = WitnessComputationCore::select(&v_16, &v_22, &v_55);
    let v_57 = v_56.truncate();
    witness_proxy.set_witness_place_u16(25usize, v_57);
    let v_59 = v_56.shr(16u32);
    let v_60 = v_59.truncate();
    witness_proxy.set_witness_place_u16(26usize, v_60);
    let v_62 = W::U16::constant(4u16);
    let v_63 = W::U16::overflowing_add(&v_0, &v_62).1;
    let v_64 = W::U16::overflowing_sub(&v_32, &v_44).1;
    let mut v_65 = v_32;
    W::U16::sub_assign(&mut v_65, &v_44);
    let v_66 = W::U16::overflowing_sub(&v_65, &v_2).1;
    let v_67 = W::Mask::or(&v_64, &v_66);
    let v_68 = W::Mask::constant(false);
    let v_69 = W::Mask::select(&v_7, &v_64, &v_68);
    let v_70 = W::Mask::select(&v_6, &v_67, &v_69);
    let v_71 = W::Mask::select(&v_16, &v_63, &v_70);
    witness_proxy.set_witness_place_boolean(28usize, v_71);
    let v_73 = W::U32::overflowing_add(&v_20, &v_21).1;
    let v_74 = W::U32::overflowing_sub(&v_34, &v_46).1;
    let v_75 = W::U32::overflowing_sub(&v_47, &v_51).1;
    let v_76 = W::Mask::or(&v_74, &v_75);
    let v_77 = W::Mask::select(&v_7, &v_74, &v_68);
    let v_78 = W::Mask::select(&v_6, &v_76, &v_77);
    let v_79 = W::Mask::select(&v_16, &v_73, &v_78);
    witness_proxy.set_witness_place_boolean(29usize, v_79);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(25usize);
    let v_1 = witness_proxy.get_witness_place(26usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let v_3 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_4 = v_2;
    W::Field::add_assign_product(&mut v_4, &v_3, &v_0);
    let mut v_5 = v_4;
    W::Field::add_assign_product(&mut v_5, &v_3, &v_1);
    let v_6 = W::U16::constant(1u16);
    let v_7 = witness_proxy.lookup::<1usize, 1usize>(&[v_5], v_6, 0usize);
    let v_8 = v_7[0usize];
    witness_proxy.set_witness_place(32usize, v_8);
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
    let v_0 = witness_proxy.get_memory_place(4usize);
    let v_1 = witness_proxy.get_memory_place(5usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let v_3 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_4 = v_2;
    W::Field::add_assign_product(&mut v_4, &v_3, &v_0);
    let v_5 = W::Field::constant(BabyBearField(268434910u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_1);
    let v_7 = W::U16::constant(5u16);
    let v_8 = witness_proxy.lookup::<1usize, 1usize>(&[v_6], v_7, 1usize);
    let v_9 = v_8[0usize];
    witness_proxy.set_witness_place(33usize, v_9);
}
#[allow(unused_variables)]
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_memory_place(11usize);
    let v_2 = witness_proxy.get_memory_place(12usize);
    let v_3 = witness_proxy.get_witness_place(29usize);
    let v_4 = witness_proxy.get_witness_place(32usize);
    let v_5 = witness_proxy.get_witness_place(33usize);
    let v_6 = W::Field::constant(BabyBearField(0u32));
    let v_7 = W::Field::constant(BabyBearField(133099247u32));
    let mut v_8 = v_6;
    W::Field::add_assign_product(&mut v_8, &v_7, &v_0);
    let v_9 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_10 = v_8;
    W::Field::add_assign_product(&mut v_10, &v_9, &v_1);
    let v_11 = W::Field::constant(BabyBearField(268434910u32));
    let mut v_12 = v_10;
    W::Field::add_assign_product(&mut v_12, &v_11, &v_2);
    let v_13 = W::Field::constant(BabyBearField(536591292u32));
    let mut v_14 = v_12;
    W::Field::add_assign_product(&mut v_14, &v_13, &v_3);
    let v_15 = W::Field::constant(BabyBearField(1073182584u32));
    let mut v_16 = v_14;
    W::Field::add_assign_product(&mut v_16, &v_15, &v_4);
    let v_17 = W::Field::constant(BabyBearField(268295646u32));
    let mut v_18 = v_16;
    W::Field::add_assign_product(&mut v_18, &v_17, &v_5);
    let v_19 = W::U16::constant(31u16);
    let v_20 = witness_proxy.lookup::<1usize, 1usize>(&[v_18], v_19, 2usize);
    let v_21 = v_20[0usize];
    witness_proxy.set_witness_place(34usize, v_21);
}
#[allow(unused_variables)]
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
    let v_0 = witness_proxy.get_memory_place_u16(26usize);
    let v_1 = witness_proxy.get_memory_place_u16(27usize);
    let v_2 = witness_proxy.get_witness_place_u16(2usize);
    let v_3 = witness_proxy.get_witness_place_u16(3usize);
    let v_4 = witness_proxy.get_witness_place_boolean(13usize);
    let v_5 = witness_proxy.get_witness_place_boolean(14usize);
    let v_6 = witness_proxy.get_witness_place_boolean(15usize);
    let v_7 = witness_proxy.get_witness_place_boolean(16usize);
    let v_8 = witness_proxy.get_memory_place_u8(2usize);
    let v_9 = witness_proxy.get_memory_place_u8(3usize);
    let v_10 = witness_proxy.get_memory_place_u8(4usize);
    let v_11 = witness_proxy.get_memory_place_u8(5usize);
    let v_12 = witness_proxy.get_witness_place_boolean(34usize);
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
    let v_45 = v_41.truncate();
    witness_proxy.set_witness_place_u16(27usize, v_45);
    let v_47 = W::U16::constant(4u16);
    let v_48 = W::U16::overflowing_add(&v_0, &v_47).1;
    let v_49 = W::U16::overflowing_add(&v_28, &v_2).1;
    let v_50 = W::U16::overflowing_add(&v_0, &v_2).1;
    let v_51 = W::U32::overflowing_add(&v_16, &v_17).1;
    let v_52 = W::Mask::select(&v_37, &v_50, &v_51);
    let v_53 = W::Mask::select(&v_4, &v_50, &v_52);
    let v_54 = W::Mask::select(&v_5, &v_49, &v_53);
    let v_55 = W::Mask::select(&v_6, &v_48, &v_54);
    witness_proxy.set_witness_place_boolean(30usize, v_55);
    let v_57 = W::U32::overflowing_add(&v_30, &v_34).1;
    let v_58 = W::U32::overflowing_add(&v_16, &v_34).1;
    let v_59 = W::Mask::select(&v_37, &v_58, &v_48);
    let v_60 = W::Mask::select(&v_4, &v_58, &v_59);
    let v_61 = W::Mask::select(&v_5, &v_57, &v_60);
    let v_62 = W::Mask::select(&v_6, &v_51, &v_61);
    witness_proxy.set_witness_place_boolean(31usize, v_62);
    witness_proxy.set_witness_place_boolean(35usize, v_37);
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
    let v_0 = witness_proxy.get_witness_place_boolean(13usize);
    let v_1 = witness_proxy.get_witness_place_boolean(14usize);
    let v_2 = witness_proxy.get_witness_place_boolean(15usize);
    let v_3 = witness_proxy.get_witness_place_boolean(16usize);
    let v_4 = W::Mask::or(&v_0, &v_1);
    let v_5 = W::Mask::or(&v_4, &v_2);
    let v_6 = W::Mask::or(&v_5, &v_3);
    witness_proxy.set_witness_place_boolean(36usize, v_6);
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
    let v_0 = witness_proxy.get_witness_place_u16(27usize);
    let v_1 = v_0.shr(1u32);
    let v_2 = v_1.get_lowest_bits(1u32);
    let v_3 = W::U16::constant(1u16);
    let v_4 = W::U16::equal(&v_2, &v_3);
    witness_proxy.set_witness_place_boolean(37usize, v_4);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(27usize);
    let v_1 = witness_proxy.get_witness_place(36usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(0usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(36usize);
    let v_1 = witness_proxy.get_witness_place(37usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(1usize, v_3);
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
    let v_0 = witness_proxy.get_memory_place(30usize);
    let v_1 = witness_proxy.get_witness_place(36usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(2usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(36usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let v_2 = W::Field::constant(BabyBearField(536870908u32));
    let mut v_3 = v_1;
    W::Field::add_assign_product(&mut v_3, &v_2, &v_0);
    witness_proxy.set_scratch_place(3usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_scratch_place(0usize);
    let v_1 = witness_proxy.get_scratch_place(1usize);
    let v_2 = witness_proxy.get_scratch_place(2usize);
    let v_3 = witness_proxy.get_scratch_place_u16(3usize);
    let v_4 = witness_proxy.lookup_enforce::<3usize>(&[v_0, v_1, v_2], v_3, 3usize);
}
#[allow(unused_variables)]
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
    let v_0 = witness_proxy.get_witness_place_boolean(13usize);
    let v_1 = witness_proxy.get_witness_place_boolean(14usize);
    let v_2 = witness_proxy.get_witness_place_boolean(15usize);
    let v_3 = witness_proxy.get_witness_place_boolean(16usize);
    let v_4 = witness_proxy.get_witness_place_boolean(17usize);
    let v_5 = W::Mask::negate(&v_4);
    let v_6 = W::Mask::and(&v_0, &v_5);
    witness_proxy.set_witness_place_boolean(38usize, v_6);
    let v_8 = W::Mask::and(&v_1, &v_5);
    witness_proxy.set_witness_place_boolean(39usize, v_8);
    let v_10 = W::Mask::and(&v_2, &v_5);
    witness_proxy.set_witness_place_boolean(40usize, v_10);
    let v_12 = W::Mask::or(&v_0, &v_1);
    let v_13 = W::Mask::or(&v_12, &v_2);
    let v_14 = W::Mask::or(&v_13, &v_3);
    let v_15 = W::Mask::and(&v_14, &v_4);
    witness_proxy.set_witness_place_boolean(41usize, v_15);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(3usize);
    let v_1 = witness_proxy.get_witness_place_boolean(19usize);
    let v_2 = W::Field::constant(BabyBearField(805306362u32));
    let v_3 = v_2.as_integer();
    let v_4 = v_3.truncate();
    let v_5 = witness_proxy.maybe_lookup::<1usize, 1usize>(&[v_0], v_4, v_1);
    let v_6 = v_5[0usize];
    witness_proxy.set_witness_place(
        42usize,
        W::Field::select(&v_1, &v_6, &witness_proxy.get_witness_place(42usize)),
    );
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(19usize);
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
        43usize,
        W::Field::select(&v_2, &v_12, &witness_proxy.get_witness_place(43usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(3usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(19usize);
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
        44usize,
        W::Field::select(&v_2, &v_12, &witness_proxy.get_witness_place(44usize)),
    );
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
    let v_0 = witness_proxy.get_witness_place_boolean(18usize);
    let v_1 = witness_proxy.get_memory_place(9usize);
    let v_2 = witness_proxy.get_memory_place(10usize);
    let v_3 = W::Field::constant(BabyBearField(134217711u32));
    let v_4 = v_3.as_integer();
    let v_5 = v_4.truncate();
    let v_6 = witness_proxy.maybe_lookup::<2usize, 1usize>(&[v_1, v_2], v_5, v_0);
    let v_7 = v_6[0usize];
    witness_proxy.set_witness_place(
        42usize,
        W::Field::select(&v_0, &v_7, &witness_proxy.get_witness_place(42usize)),
    );
}
#[allow(unused_variables)]
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(18usize);
    let v_3 = witness_proxy.get_memory_place(2usize);
    let v_4 = witness_proxy.get_witness_place(42usize);
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
        43usize,
        W::Field::select(&v_2, &v_13, &witness_proxy.get_witness_place(43usize)),
    );
    let v_15 = v_12[1usize];
    witness_proxy.set_witness_place(
        44usize,
        W::Field::select(&v_2, &v_15, &witness_proxy.get_witness_place(44usize)),
    );
    let v_17 = v_12[2usize];
    witness_proxy.set_witness_place(
        45usize,
        W::Field::select(&v_2, &v_17, &witness_proxy.get_witness_place(45usize)),
    );
    let v_19 = v_12[3usize];
    witness_proxy.set_witness_place(
        46usize,
        W::Field::select(&v_2, &v_19, &witness_proxy.get_witness_place(46usize)),
    );
}
#[allow(unused_variables)]
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(18usize);
    let v_3 = witness_proxy.get_memory_place(3usize);
    let v_4 = witness_proxy.get_witness_place(42usize);
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
        47usize,
        W::Field::select(&v_2, &v_13, &witness_proxy.get_witness_place(47usize)),
    );
    let v_15 = v_12[1usize];
    witness_proxy.set_witness_place(
        48usize,
        W::Field::select(&v_2, &v_15, &witness_proxy.get_witness_place(48usize)),
    );
    let v_17 = v_12[2usize];
    witness_proxy.set_witness_place(
        49usize,
        W::Field::select(&v_2, &v_17, &witness_proxy.get_witness_place(49usize)),
    );
    let v_19 = v_12[3usize];
    witness_proxy.set_witness_place(
        50usize,
        W::Field::select(&v_2, &v_19, &witness_proxy.get_witness_place(50usize)),
    );
}
#[allow(unused_variables)]
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(18usize);
    let v_3 = witness_proxy.get_memory_place(4usize);
    let v_4 = witness_proxy.get_witness_place(42usize);
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
        51usize,
        W::Field::select(&v_2, &v_14, &witness_proxy.get_witness_place(51usize)),
    );
    let v_16 = v_13[1usize];
    witness_proxy.set_witness_place(
        52usize,
        W::Field::select(&v_2, &v_16, &witness_proxy.get_witness_place(52usize)),
    );
    let v_18 = v_13[2usize];
    witness_proxy.set_witness_place(
        53usize,
        W::Field::select(&v_2, &v_18, &witness_proxy.get_witness_place(53usize)),
    );
    let v_20 = v_13[3usize];
    witness_proxy.set_witness_place(
        54usize,
        W::Field::select(&v_2, &v_20, &witness_proxy.get_witness_place(54usize)),
    );
}
#[allow(unused_variables)]
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(18usize);
    let v_3 = witness_proxy.get_memory_place(5usize);
    let v_4 = witness_proxy.get_witness_place(42usize);
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
        55usize,
        W::Field::select(&v_2, &v_14, &witness_proxy.get_witness_place(55usize)),
    );
    let v_16 = v_13[1usize];
    witness_proxy.set_witness_place(
        56usize,
        W::Field::select(&v_2, &v_16, &witness_proxy.get_witness_place(56usize)),
    );
    let v_18 = v_13[2usize];
    witness_proxy.set_witness_place(
        57usize,
        W::Field::select(&v_2, &v_18, &witness_proxy.get_witness_place(57usize)),
    );
    let v_20 = v_13[3usize];
    witness_proxy.set_witness_place(
        58usize,
        W::Field::select(&v_2, &v_20, &witness_proxy.get_witness_place(58usize)),
    );
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
    let v_0 = witness_proxy.get_witness_place(3usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = witness_proxy.get_memory_place(9usize);
    let v_4 = W::Field::constant(BabyBearField(0u32));
    let mut v_5 = v_4;
    W::Field::add_assign_product(&mut v_5, &v_0, &v_2);
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_1, &v_3);
    witness_proxy.set_scratch_place(4usize, v_6);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_memory_place(10usize);
    let v_3 = witness_proxy.get_witness_place(42usize);
    let v_4 = W::Field::constant(BabyBearField(0u32));
    let mut v_5 = v_4;
    W::Field::add_assign_product(&mut v_5, &v_0, &v_2);
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_1, &v_3);
    witness_proxy.set_scratch_place(5usize, v_6);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(42usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(6usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let v_3 = W::Field::constant(BabyBearField(134217711u32));
    let mut v_4 = v_2;
    W::Field::add_assign_product(&mut v_4, &v_3, &v_0);
    let v_5 = W::Field::constant(BabyBearField(805306362u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_1);
    witness_proxy.set_scratch_place(7usize, v_6);
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
    let v_0 = witness_proxy.get_scratch_place(4usize);
    let v_1 = witness_proxy.get_scratch_place(5usize);
    let v_2 = witness_proxy.get_scratch_place(6usize);
    let v_3 = witness_proxy.get_scratch_place_u16(7usize);
    let v_4 = witness_proxy.lookup_enforce::<3usize>(&[v_0, v_1, v_2], v_3, 4usize);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_memory_place(2usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(8usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = witness_proxy.get_memory_place(2usize);
    let v_4 = witness_proxy.get_memory_place(9usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_2);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_2, &v_4);
    witness_proxy.set_scratch_place(9usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = witness_proxy.get_witness_place(42usize);
    let v_4 = witness_proxy.get_witness_place(43usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_1);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_2, &v_4);
    witness_proxy.set_scratch_place(10usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(11usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(43usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(12usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(44usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(13usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_0, &v_2);
    let v_5 = W::Field::constant(BabyBearField(402653165u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_1);
    witness_proxy.set_scratch_place(16usize, v_6);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_memory_place(3usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_1, &v_2);
    let mut v_5 = v_4;
    W::Field::add_assign(&mut v_5, &v_0);
    witness_proxy.set_scratch_place(17usize, v_5);
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
    let v_0 = witness_proxy.get_witness_place(3usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = witness_proxy.get_memory_place(3usize);
    let v_4 = witness_proxy.get_memory_place(10usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_2);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_2, &v_4);
    witness_proxy.set_scratch_place(18usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = witness_proxy.get_witness_place(42usize);
    let v_4 = witness_proxy.get_witness_place(44usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_1);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_2, &v_4);
    witness_proxy.set_scratch_place(19usize, v_8);
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(20usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(47usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(21usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(48usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(22usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(49usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(23usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(50usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(24usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_0, &v_2);
    let v_5 = W::Field::constant(BabyBearField(402653165u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_1);
    witness_proxy.set_scratch_place(25usize, v_6);
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
    let v_0 = witness_proxy.get_scratch_place(17usize);
    let v_1 = witness_proxy.get_scratch_place(18usize);
    let v_2 = witness_proxy.get_scratch_place(19usize);
    let v_3 = witness_proxy.get_scratch_place(20usize);
    let v_4 = witness_proxy.get_scratch_place(21usize);
    let v_5 = witness_proxy.get_scratch_place(22usize);
    let v_6 = witness_proxy.get_scratch_place(23usize);
    let v_7 = witness_proxy.get_scratch_place(24usize);
    let v_8 = witness_proxy.get_scratch_place_u16(25usize);
    let v_9 = witness_proxy.lookup_enforce::<8usize>(
        &[v_0, v_1, v_2, v_3, v_4, v_5, v_6, v_7],
        v_8,
        6usize,
    );
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_memory_place(4usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_1, &v_2);
    let v_5 = W::Field::constant(BabyBearField(536870908u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_0);
    witness_proxy.set_scratch_place(26usize, v_6);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_memory_place(4usize);
    let v_3 = witness_proxy.get_memory_place(11usize);
    let v_4 = witness_proxy.get_witness_place(42usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_2);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_1, &v_4);
    witness_proxy.set_scratch_place(27usize, v_8);
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(29usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(51usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(30usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(52usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(31usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(53usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(32usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(54usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(33usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_0, &v_2);
    let v_5 = W::Field::constant(BabyBearField(402653165u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_1);
    witness_proxy.set_scratch_place(34usize, v_6);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_memory_place(5usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_1, &v_2);
    let v_5 = W::Field::constant(BabyBearField(805306362u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_0);
    witness_proxy.set_scratch_place(35usize, v_6);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = witness_proxy.get_memory_place(5usize);
    let v_3 = witness_proxy.get_memory_place(12usize);
    let v_4 = witness_proxy.get_witness_place(42usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_2);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_1, &v_4);
    witness_proxy.set_scratch_place(36usize, v_8);
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(38usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_59<
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(55usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(39usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(56usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(40usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(57usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(41usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(58usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(42usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(4usize);
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_0, &v_2);
    let v_5 = W::Field::constant(BabyBearField(402653165u32));
    let mut v_6 = v_4;
    W::Field::add_assign_product(&mut v_6, &v_5, &v_1);
    witness_proxy.set_scratch_place(43usize, v_6);
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
    let v_0 = witness_proxy.get_witness_place_u16(2usize);
    let v_1 = witness_proxy.get_witness_place_u16(3usize);
    let v_2 = witness_proxy.get_memory_place_boolean(13usize);
    let v_3 = witness_proxy.get_memory_place_boolean(20usize);
    let v_4 = witness_proxy.get_memory_place_u8(2usize);
    let v_5 = witness_proxy.get_memory_place_u8(3usize);
    let v_6 = witness_proxy.get_memory_place_u8(4usize);
    let v_7 = witness_proxy.get_memory_place_u8(5usize);
    let v_8 = W::Mask::or(&v_2, &v_3);
    witness_proxy.set_witness_place_boolean(59usize, v_8);
    let v_10 = v_5.widen();
    let v_11 = v_10.shl(8u32);
    let v_12 = v_4.widen();
    let mut v_13 = v_11;
    W::U16::add_assign(&mut v_13, &v_12);
    let v_14 = W::U16::overflowing_add(&v_13, &v_0).1;
    let v_15 = W::Mask::constant(false);
    let v_16 = W::Mask::select(&v_8, &v_14, &v_15);
    witness_proxy.set_witness_place_boolean(60usize, v_16);
    let v_18 = v_7.widen();
    let v_19 = v_18.shl(8u32);
    let v_20 = v_6.widen();
    let mut v_21 = v_19;
    W::U16::add_assign(&mut v_21, &v_20);
    let v_22 = W::U16::overflowing_add(&v_21, &v_1).1;
    let mut v_23 = v_21;
    W::U16::add_assign(&mut v_23, &v_1);
    let v_24 = W::U32::from_mask(v_14);
    let v_25 = v_24.truncate();
    let v_26 = W::U16::overflowing_add(&v_23, &v_25).1;
    let v_27 = W::Mask::or(&v_22, &v_26);
    let v_28 = W::Mask::select(&v_8, &v_27, &v_15);
    witness_proxy.set_witness_place_boolean(61usize, v_28);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_memory_place(13usize);
    let v_1 = witness_proxy.get_memory_place(20usize);
    let v_2 = witness_proxy.get_memory_place(15usize);
    let v_3 = witness_proxy.get_memory_place(22usize);
    let v_4 = W::Field::constant(BabyBearField(0u32));
    let mut v_5 = v_4;
    W::Field::add_assign_product(&mut v_5, &v_0, &v_2);
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_1, &v_3);
    let v_7 = v_6.as_integer();
    let v_8 = v_7.shr(6u32);
    let v_9 = W::U32::constant(0u32);
    let v_10 = W::U32::equal(&v_8, &v_9);
    witness_proxy.set_witness_place_boolean(62usize, v_10);
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
    let v_0 = witness_proxy.get_memory_place(13usize);
    let v_1 = witness_proxy.get_memory_place(20usize);
    let v_2 = witness_proxy.get_memory_place(15usize);
    let v_3 = witness_proxy.get_memory_place(22usize);
    let v_4 = witness_proxy.get_witness_place(62usize);
    let v_5 = W::Field::constant(BabyBearField(939524233u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_2);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let v_8 = W::Field::constant(BabyBearField(268295646u32));
    let mut v_9 = v_7;
    W::Field::add_assign_product(&mut v_9, &v_8, &v_4);
    witness_proxy.set_scratch_place(44usize, v_9);
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
    let v_0 = witness_proxy.get_witness_place_boolean(59usize);
    let v_1 = witness_proxy.get_witness_place_boolean(62usize);
    let v_2 = W::Mask::and(&v_0, &v_1);
    witness_proxy.set_witness_place_boolean(63usize, v_2);
    let v_4 = W::Mask::negate(&v_1);
    let v_5 = W::Mask::and(&v_0, &v_4);
    witness_proxy.set_witness_place_boolean(64usize, v_5);
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
    let v_0 = witness_proxy.get_memory_place(13usize);
    let v_1 = witness_proxy.get_memory_place(20usize);
    let v_2 = witness_proxy.get_memory_place(14usize);
    let v_3 = witness_proxy.get_memory_place(15usize);
    let v_4 = witness_proxy.get_memory_place(21usize);
    let v_5 = witness_proxy.get_memory_place(22usize);
    let v_6 = W::Field::constant(BabyBearField(0u32));
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_0, &v_2);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_1, &v_4);
    let v_9 = W::Field::constant(BabyBearField(268295646u32));
    let mut v_10 = v_0;
    W::Field::mul_assign(&mut v_10, &v_9);
    let mut v_11 = v_8;
    W::Field::add_assign_product(&mut v_11, &v_10, &v_3);
    let mut v_12 = v_1;
    W::Field::mul_assign(&mut v_12, &v_9);
    let mut v_13 = v_11;
    W::Field::add_assign_product(&mut v_13, &v_12, &v_5);
    witness_proxy.set_scratch_place(45usize, v_13);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_witness_place(62usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(46usize, v_2);
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
    let v_0 = witness_proxy.get_scratch_place(45usize);
    let v_1 = witness_proxy.get_scratch_place(46usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(47usize, v_3);
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
    let v_0 = witness_proxy.get_memory_place(9usize);
    let v_1 = witness_proxy.get_memory_place(10usize);
    let v_2 = witness_proxy.get_memory_place(23usize);
    let v_3 = witness_proxy.get_witness_place(59usize);
    let v_4 = witness_proxy.get_witness_place(64usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_2, &v_3);
    let mut v_7 = v_0;
    W::Field::mul_assign(&mut v_7, &v_4);
    let mut v_8 = v_6;
    W::Field::sub_assign(&mut v_8, &v_7);
    let v_9 = W::Field::constant(BabyBearField(1744831011u32));
    let mut v_10 = v_1;
    W::Field::mul_assign(&mut v_10, &v_9);
    let mut v_11 = v_8;
    W::Field::add_assign_product(&mut v_11, &v_10, &v_4);
    witness_proxy.set_scratch_place(48usize, v_11);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_scratch_place(48usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(49usize, v_2);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_memory_place(11usize);
    let v_1 = witness_proxy.get_memory_place(12usize);
    let v_2 = witness_proxy.get_memory_place(24usize);
    let v_3 = witness_proxy.get_witness_place(59usize);
    let v_4 = witness_proxy.get_witness_place(64usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_2, &v_3);
    let mut v_7 = v_0;
    W::Field::mul_assign(&mut v_7, &v_4);
    let mut v_8 = v_6;
    W::Field::sub_assign(&mut v_8, &v_7);
    let v_9 = W::Field::constant(BabyBearField(1744831011u32));
    let mut v_10 = v_1;
    W::Field::mul_assign(&mut v_10, &v_9);
    let mut v_11 = v_8;
    W::Field::add_assign_product(&mut v_11, &v_10, &v_4);
    witness_proxy.set_scratch_place(50usize, v_11);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_scratch_place(50usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(51usize, v_2);
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
    let v_0 = witness_proxy.get_memory_place(25usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(52usize, v_2);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_76<
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
    let v_0 = witness_proxy.get_witness_place(63usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(53usize, v_2);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_77<
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
    let v_0 = witness_proxy.get_scratch_place(52usize);
    let v_1 = witness_proxy.get_scratch_place(53usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let v_3 = W::Field::constant(BabyBearField(1073741752u32));
    let mut v_4 = v_0;
    W::Field::mul_assign(&mut v_4, &v_3);
    let mut v_5 = v_2;
    W::Field::add_assign_product(&mut v_5, &v_4, &v_1);
    witness_proxy.set_scratch_place(54usize, v_5);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_78<
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
    let v_0 = witness_proxy.get_scratch_place(47usize);
    let v_1 = witness_proxy.get_scratch_place(49usize);
    let v_2 = witness_proxy.get_scratch_place(51usize);
    let v_3 = witness_proxy.get_scratch_place_u16(54usize);
    let v_4 = witness_proxy.lookup_enforce::<3usize>(&[v_0, v_1, v_2], v_3, 9usize);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_79<
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
    let v_0 = witness_proxy.get_memory_place_u16(21usize);
    let v_1 = v_0.get_lowest_bits(1u32);
    let v_2 = W::U16::constant(1u16);
    let v_3 = W::U16::equal(&v_1, &v_2);
    witness_proxy.set_witness_place_boolean(65usize, v_3);
    let v_5 = v_0.shr(1u32);
    let v_6 = v_5.get_lowest_bits(1u32);
    let v_7 = W::U16::equal(&v_6, &v_2);
    witness_proxy.set_witness_place_boolean(66usize, v_7);
    let v_9 = v_0.shr(2u32);
    witness_proxy.set_witness_place_u16(67usize, v_9);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_80<
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
    witness_proxy.set_witness_place_boolean(68usize, v_2);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_81<
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
    let v_1 = witness_proxy.get_witness_place_boolean(13usize);
    let v_2 = witness_proxy.get_witness_place_boolean(14usize);
    let v_3 = witness_proxy.get_witness_place_boolean(15usize);
    let v_4 = witness_proxy.get_witness_place_boolean(16usize);
    let v_5 = W::Mask::or(&v_1, &v_2);
    let v_6 = W::Mask::or(&v_5, &v_3);
    let v_7 = W::Mask::or(&v_6, &v_4);
    let v_8 = W::Mask::negate(&v_7);
    let v_9 = W::Mask::and(&v_0, &v_8);
    witness_proxy.set_witness_place_boolean(69usize, v_9);
}
#[allow(unused_variables)]
fn eval_fn_82<
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
    let v_13 = witness_proxy.get_witness_place_boolean(18usize);
    let v_14 = witness_proxy.get_witness_place_boolean(19usize);
    let v_15 = witness_proxy.get_memory_place_boolean(13usize);
    let v_16 = witness_proxy.get_memory_place_boolean(20usize);
    let v_17 = W::Mask::or(&v_1, &v_2);
    let v_18 = W::Mask::or(&v_17, &v_3);
    let v_19 = W::Mask::or(&v_18, &v_4);
    let v_20 = W::Mask::or(&v_19, &v_5);
    let v_21 = W::Mask::or(&v_20, &v_6);
    let v_22 = W::Mask::or(&v_21, &v_7);
    let v_23 = W::Mask::or(&v_22, &v_8);
    let v_24 = W::Mask::or(&v_23, &v_9);
    let v_25 = W::Mask::or(&v_24, &v_10);
    let v_26 = W::Mask::or(&v_25, &v_11);
    let v_27 = W::Mask::or(&v_26, &v_12);
    let v_28 = W::Mask::or(&v_27, &v_13);
    let v_29 = W::Mask::or(&v_28, &v_14);
    let v_30 = W::Mask::or(&v_29, &v_15);
    let v_31 = W::Mask::or(&v_30, &v_16);
    let v_32 = W::Mask::and(&v_0, &v_31);
    witness_proxy.set_witness_place_boolean(70usize, v_32);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_83<
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
    let v_1 = witness_proxy.get_witness_place_boolean(19usize);
    let v_2 = witness_proxy.get_memory_place(4usize);
    let v_3 = witness_proxy.get_memory_place(11usize);
    let v_4 = witness_proxy.get_witness_place(42usize);
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
        45usize,
        W::Field::select(&v_1, &v_12, &witness_proxy.get_witness_place(45usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_84<
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
    let v_1 = witness_proxy.get_witness_place_boolean(19usize);
    let v_2 = witness_proxy.get_memory_place(5usize);
    let v_3 = witness_proxy.get_memory_place(12usize);
    let v_4 = witness_proxy.get_witness_place(42usize);
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
        46usize,
        W::Field::select(&v_1, &v_12, &witness_proxy.get_witness_place(46usize)),
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_85<
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(45usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(14usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_86<
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
    let v_0 = witness_proxy.get_witness_place(18usize);
    let v_1 = witness_proxy.get_witness_place(46usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(15usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_87<
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
    let v_0 = witness_proxy.get_scratch_place(8usize);
    let v_1 = witness_proxy.get_scratch_place(9usize);
    let v_2 = witness_proxy.get_scratch_place(10usize);
    let v_3 = witness_proxy.get_scratch_place(11usize);
    let v_4 = witness_proxy.get_scratch_place(12usize);
    let v_5 = witness_proxy.get_scratch_place(13usize);
    let v_6 = witness_proxy.get_scratch_place(14usize);
    let v_7 = witness_proxy.get_scratch_place(15usize);
    let v_8 = witness_proxy.get_scratch_place_u16(16usize);
    let v_9 = witness_proxy.lookup_enforce::<8usize>(
        &[v_0, v_1, v_2, v_3, v_4, v_5, v_6, v_7],
        v_8,
        5usize,
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_88<
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
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = witness_proxy.get_witness_place(42usize);
    let v_4 = witness_proxy.get_witness_place(45usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_1);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_2, &v_4);
    witness_proxy.set_scratch_place(28usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_89<
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
    let v_0 = witness_proxy.get_scratch_place(26usize);
    let v_1 = witness_proxy.get_scratch_place(27usize);
    let v_2 = witness_proxy.get_scratch_place(28usize);
    let v_3 = witness_proxy.get_scratch_place(29usize);
    let v_4 = witness_proxy.get_scratch_place(30usize);
    let v_5 = witness_proxy.get_scratch_place(31usize);
    let v_6 = witness_proxy.get_scratch_place(32usize);
    let v_7 = witness_proxy.get_scratch_place(33usize);
    let v_8 = witness_proxy.get_scratch_place_u16(34usize);
    let v_9 = witness_proxy.lookup_enforce::<8usize>(
        &[v_0, v_1, v_2, v_3, v_4, v_5, v_6, v_7],
        v_8,
        7usize,
    );
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_90<
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
    let v_1 = witness_proxy.get_witness_place(18usize);
    let v_2 = witness_proxy.get_witness_place(19usize);
    let v_3 = witness_proxy.get_witness_place(42usize);
    let v_4 = witness_proxy.get_witness_place(46usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_1);
    let mut v_7 = v_6;
    W::Field::add_assign_product(&mut v_7, &v_1, &v_3);
    let mut v_8 = v_7;
    W::Field::add_assign_product(&mut v_8, &v_2, &v_4);
    witness_proxy.set_scratch_place(37usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_91<
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
    let v_0 = witness_proxy.get_scratch_place(35usize);
    let v_1 = witness_proxy.get_scratch_place(36usize);
    let v_2 = witness_proxy.get_scratch_place(37usize);
    let v_3 = witness_proxy.get_scratch_place(38usize);
    let v_4 = witness_proxy.get_scratch_place(39usize);
    let v_5 = witness_proxy.get_scratch_place(40usize);
    let v_6 = witness_proxy.get_scratch_place(41usize);
    let v_7 = witness_proxy.get_scratch_place(42usize);
    let v_8 = witness_proxy.get_scratch_place_u16(43usize);
    let v_9 = witness_proxy.lookup_enforce::<8usize>(
        &[v_0, v_1, v_2, v_3, v_4, v_5, v_6, v_7],
        v_8,
        8usize,
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
    eval_fn_59(witness_proxy);
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
    eval_fn_76(witness_proxy);
    eval_fn_77(witness_proxy);
    eval_fn_78(witness_proxy);
    eval_fn_79(witness_proxy);
    eval_fn_80(witness_proxy);
    eval_fn_81(witness_proxy);
    eval_fn_82(witness_proxy);
    eval_fn_83(witness_proxy);
    eval_fn_84(witness_proxy);
    eval_fn_85(witness_proxy);
    eval_fn_86(witness_proxy);
    eval_fn_87(witness_proxy);
    eval_fn_88(witness_proxy);
    eval_fn_89(witness_proxy);
    eval_fn_90(witness_proxy);
    eval_fn_91(witness_proxy);
}
