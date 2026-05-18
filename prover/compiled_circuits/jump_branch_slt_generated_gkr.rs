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
    let v_0 = witness_proxy.get_memory_place_u16(22usize);
    let v_1 = witness_proxy.get_memory_place_u16(23usize);
    let v_2 = witness_proxy.get_witness_place_u16(0usize);
    let v_3 = witness_proxy.get_witness_place_u16(1usize);
    let v_4 = witness_proxy.get_witness_place_boolean(3usize);
    let v_5 = witness_proxy.get_witness_place_boolean(4usize);
    let v_6 = witness_proxy.get_witness_place_boolean(5usize);
    let v_7 = witness_proxy.get_witness_place_boolean(6usize);
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
    witness_proxy.set_witness_place_u16(8usize, v_57);
    let v_59 = v_56.shr(16u32);
    let v_60 = v_59.truncate();
    witness_proxy.set_witness_place_u16(9usize, v_60);
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
    witness_proxy.set_witness_place_boolean(11usize, v_71);
    let v_73 = W::U32::overflowing_add(&v_20, &v_21).1;
    let v_74 = W::U32::overflowing_sub(&v_34, &v_46).1;
    let v_75 = W::U32::overflowing_sub(&v_47, &v_51).1;
    let v_76 = W::Mask::or(&v_74, &v_75);
    let v_77 = W::Mask::select(&v_7, &v_74, &v_68);
    let v_78 = W::Mask::select(&v_6, &v_76, &v_77);
    let v_79 = W::Mask::select(&v_16, &v_73, &v_78);
    witness_proxy.set_witness_place_boolean(12usize, v_79);
}
#[allow(unused_variables)]
#[inline(always)]
fn eval_fn_2<'a, 'b: 'a, W: WitnessTypeSet<BabyBearField>, P: WitnessProxy<BabyBearField, W> + 'b>(
    witness_proxy: &'a mut P,
) where
    W::Field: Copy,
    W::Mask: Copy,
    W::U32: Copy,
    W::U16: Copy,
    W::U8: Copy,
    W::I32: Copy,
{
    let v_0 = witness_proxy.get_witness_place(8usize);
    let v_1 = witness_proxy.get_witness_place(9usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let v_3 = W::Field::constant(BabyBearField(268435454u32));
    let mut v_4 = v_2;
    W::Field::add_assign_product(&mut v_4, &v_3, &v_0);
    let mut v_5 = v_4;
    W::Field::add_assign_product(&mut v_5, &v_3, &v_1);
    let v_6 = W::U16::constant(1u16);
    let v_7 = witness_proxy.lookup::<1usize, 1usize>(&[v_5], v_6, 0usize);
    let v_8 = v_7[0usize];
    witness_proxy.set_witness_place(15usize, v_8);
}
#[allow(unused_variables)]
#[inline(always)]
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
    witness_proxy.set_witness_place(16usize, v_9);
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
    let v_0 = witness_proxy.get_witness_place(2usize);
    let v_1 = witness_proxy.get_memory_place(11usize);
    let v_2 = witness_proxy.get_memory_place(12usize);
    let v_3 = witness_proxy.get_witness_place(12usize);
    let v_4 = witness_proxy.get_witness_place(15usize);
    let v_5 = witness_proxy.get_witness_place(16usize);
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
    witness_proxy.set_witness_place(17usize, v_21);
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
    let v_0 = witness_proxy.get_memory_place_u16(22usize);
    let v_1 = witness_proxy.get_memory_place_u16(23usize);
    let v_2 = witness_proxy.get_witness_place_u16(0usize);
    let v_3 = witness_proxy.get_witness_place_u16(1usize);
    let v_4 = witness_proxy.get_witness_place_boolean(3usize);
    let v_5 = witness_proxy.get_witness_place_boolean(4usize);
    let v_6 = witness_proxy.get_witness_place_boolean(5usize);
    let v_7 = witness_proxy.get_witness_place_boolean(6usize);
    let v_8 = witness_proxy.get_memory_place_u8(2usize);
    let v_9 = witness_proxy.get_memory_place_u8(3usize);
    let v_10 = witness_proxy.get_memory_place_u8(4usize);
    let v_11 = witness_proxy.get_memory_place_u8(5usize);
    let v_12 = witness_proxy.get_witness_place_boolean(17usize);
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
    witness_proxy.set_witness_place_u16(10usize, v_45);
    let v_47 = W::U16::constant(4u16);
    let v_48 = W::U16::overflowing_add(&v_0, &v_47).1;
    let v_49 = W::U16::overflowing_add(&v_28, &v_2).1;
    let v_50 = W::U16::overflowing_add(&v_0, &v_2).1;
    let v_51 = W::U32::overflowing_add(&v_16, &v_17).1;
    let v_52 = W::Mask::select(&v_37, &v_50, &v_51);
    let v_53 = W::Mask::select(&v_4, &v_50, &v_52);
    let v_54 = W::Mask::select(&v_5, &v_49, &v_53);
    let v_55 = W::Mask::select(&v_6, &v_48, &v_54);
    witness_proxy.set_witness_place_boolean(13usize, v_55);
    let v_57 = W::U32::overflowing_add(&v_30, &v_34).1;
    let v_58 = W::U32::overflowing_add(&v_16, &v_34).1;
    let v_59 = W::Mask::select(&v_37, &v_58, &v_48);
    let v_60 = W::Mask::select(&v_4, &v_58, &v_59);
    let v_61 = W::Mask::select(&v_5, &v_57, &v_60);
    let v_62 = W::Mask::select(&v_6, &v_51, &v_61);
    witness_proxy.set_witness_place_boolean(14usize, v_62);
    witness_proxy.set_witness_place_boolean(18usize, v_37);
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
    let v_0 = witness_proxy.get_witness_place_boolean(3usize);
    let v_1 = witness_proxy.get_witness_place_boolean(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(5usize);
    let v_3 = witness_proxy.get_witness_place_boolean(6usize);
    let v_4 = W::Mask::or(&v_0, &v_1);
    let v_5 = W::Mask::or(&v_4, &v_2);
    let v_6 = W::Mask::or(&v_5, &v_3);
    witness_proxy.set_witness_place_boolean(19usize, v_6);
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
    let v_0 = witness_proxy.get_witness_place_u16(10usize);
    let v_1 = v_0.shr(1u32);
    let v_2 = v_1.get_lowest_bits(1u32);
    let v_3 = W::U16::constant(1u16);
    let v_4 = W::U16::equal(&v_2, &v_3);
    witness_proxy.set_witness_place_boolean(20usize, v_4);
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
    let v_0 = witness_proxy.get_witness_place(10usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(0usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = witness_proxy.get_witness_place(20usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(1usize, v_3);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_memory_place(26usize);
    let v_1 = witness_proxy.get_witness_place(19usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(2usize, v_3);
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
    let v_0 = witness_proxy.get_witness_place(19usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let v_2 = W::Field::constant(BabyBearField(536870908u32));
    let mut v_3 = v_1;
    W::Field::add_assign_product(&mut v_3, &v_2, &v_0);
    witness_proxy.set_scratch_place(3usize, v_3);
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
    let v_0 = witness_proxy.get_scratch_place(0usize);
    let v_1 = witness_proxy.get_scratch_place(1usize);
    let v_2 = witness_proxy.get_scratch_place(2usize);
    let v_3 = witness_proxy.get_scratch_place_u16(3usize);
    let v_4 = witness_proxy.lookup_enforce::<3usize>(&[v_0, v_1, v_2], v_3, 3usize);
}
#[allow(unused_variables)]
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
    let v_0 = witness_proxy.get_witness_place_boolean(3usize);
    let v_1 = witness_proxy.get_witness_place_boolean(4usize);
    let v_2 = witness_proxy.get_witness_place_boolean(5usize);
    let v_3 = witness_proxy.get_witness_place_boolean(6usize);
    let v_4 = witness_proxy.get_witness_place_boolean(7usize);
    let v_5 = W::Mask::negate(&v_4);
    let v_6 = W::Mask::and(&v_0, &v_5);
    witness_proxy.set_witness_place_boolean(21usize, v_6);
    let v_8 = W::Mask::and(&v_1, &v_5);
    witness_proxy.set_witness_place_boolean(22usize, v_8);
    let v_10 = W::Mask::and(&v_2, &v_5);
    witness_proxy.set_witness_place_boolean(23usize, v_10);
    let v_12 = W::Mask::or(&v_0, &v_1);
    let v_13 = W::Mask::or(&v_12, &v_2);
    let v_14 = W::Mask::or(&v_13, &v_3);
    let v_15 = W::Mask::and(&v_14, &v_4);
    witness_proxy.set_witness_place_boolean(24usize, v_15);
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
    eval_fn_2(witness_proxy);
    eval_fn_3(witness_proxy);
    eval_fn_4(witness_proxy);
    eval_fn_5(witness_proxy);
    eval_fn_6(witness_proxy);
    eval_fn_7(witness_proxy);
    eval_fn_9(witness_proxy);
    eval_fn_10(witness_proxy);
    eval_fn_11(witness_proxy);
    eval_fn_12(witness_proxy);
    eval_fn_13(witness_proxy);
    eval_fn_14(witness_proxy);
}
