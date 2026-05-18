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
    let v_0 = witness_proxy.get_witness_place_u16(2usize);
    let v_1 = witness_proxy.get_witness_place_u16(3usize);
    let v_2 = witness_proxy.get_memory_place_boolean(13usize);
    let v_3 = witness_proxy.get_memory_place_u8(2usize);
    let v_4 = witness_proxy.get_memory_place_u8(3usize);
    let v_5 = witness_proxy.get_memory_place_u8(4usize);
    let v_6 = witness_proxy.get_memory_place_u8(5usize);
    let v_7 = W::Mask::negate(&v_2);
    let v_8 = W::Mask::or(&v_7, &v_2);
    witness_proxy.set_witness_place_boolean(4usize, v_8);
    let v_10 = v_4.widen();
    let v_11 = v_10.shl(8u32);
    let v_12 = v_3.widen();
    let mut v_13 = v_11;
    W::U16::add_assign(&mut v_13, &v_12);
    let v_14 = W::U16::overflowing_add(&v_13, &v_0).1;
    let v_15 = W::Mask::constant(false);
    let v_16 = W::Mask::select(&v_8, &v_14, &v_15);
    witness_proxy.set_witness_place_boolean(5usize, v_16);
    let v_18 = v_6.widen();
    let v_19 = v_18.shl(8u32);
    let v_20 = v_5.widen();
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
    witness_proxy.set_witness_place_boolean(6usize, v_28);
}
#[allow(unused_variables)]
#[inline(always)]
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
    let v_0 = witness_proxy.get_memory_place(13usize);
    let v_1 = witness_proxy.get_memory_place(15usize);
    let v_2 = witness_proxy.get_memory_place(21usize);
    let v_3 = W::Field::constant(BabyBearField(0u32));
    let mut v_4 = v_3;
    W::Field::add_assign_product(&mut v_4, &v_0, &v_2);
    let mut v_5 = v_0;
    W::Field::mul_assign(&mut v_5, &v_1);
    let mut v_6 = v_4;
    W::Field::sub_assign(&mut v_6, &v_5);
    let mut v_7 = v_6;
    W::Field::add_assign(&mut v_7, &v_1);
    let v_8 = v_7.as_integer();
    let v_9 = v_8.shr(6u32);
    let v_10 = W::U32::constant(0u32);
    let v_11 = W::U32::equal(&v_9, &v_10);
    witness_proxy.set_witness_place_boolean(7usize, v_11);
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
    let v_0 = witness_proxy.get_memory_place(13usize);
    let v_1 = witness_proxy.get_memory_place(15usize);
    let v_2 = witness_proxy.get_memory_place(21usize);
    let v_3 = witness_proxy.get_witness_place(7usize);
    let v_4 = W::Field::constant(BabyBearField(939524233u32));
    let mut v_5 = v_4;
    W::Field::add_assign_product(&mut v_5, &v_0, &v_2);
    let mut v_6 = v_0;
    W::Field::mul_assign(&mut v_6, &v_1);
    let mut v_7 = v_5;
    W::Field::sub_assign(&mut v_7, &v_6);
    let mut v_8 = v_7;
    W::Field::add_assign(&mut v_8, &v_1);
    let v_9 = W::Field::constant(BabyBearField(268295646u32));
    let mut v_10 = v_8;
    W::Field::add_assign_product(&mut v_10, &v_9, &v_3);
    witness_proxy.set_scratch_place(0usize, v_10);
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
    let v_0 = witness_proxy.get_witness_place_boolean(4usize);
    let v_1 = witness_proxy.get_witness_place_boolean(7usize);
    let v_2 = W::Mask::and(&v_0, &v_1);
    witness_proxy.set_witness_place_boolean(8usize, v_2);
    let v_4 = W::Mask::negate(&v_1);
    let v_5 = W::Mask::and(&v_0, &v_4);
    witness_proxy.set_witness_place_boolean(9usize, v_5);
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
    let v_0 = witness_proxy.get_memory_place(13usize);
    let v_1 = witness_proxy.get_memory_place(14usize);
    let v_2 = witness_proxy.get_memory_place(15usize);
    let v_3 = witness_proxy.get_memory_place(20usize);
    let v_4 = witness_proxy.get_memory_place(21usize);
    let v_5 = W::Field::constant(BabyBearField(0u32));
    let mut v_6 = v_5;
    W::Field::add_assign_product(&mut v_6, &v_0, &v_3);
    let mut v_7 = v_0;
    W::Field::mul_assign(&mut v_7, &v_1);
    let mut v_8 = v_6;
    W::Field::sub_assign(&mut v_8, &v_7);
    let v_9 = W::Field::constant(BabyBearField(1744970275u32));
    let mut v_10 = v_0;
    W::Field::mul_assign(&mut v_10, &v_9);
    let mut v_11 = v_8;
    W::Field::add_assign_product(&mut v_11, &v_10, &v_2);
    let v_12 = W::Field::constant(BabyBearField(268295646u32));
    let mut v_13 = v_0;
    W::Field::mul_assign(&mut v_13, &v_12);
    let mut v_14 = v_11;
    W::Field::add_assign_product(&mut v_14, &v_13, &v_4);
    let mut v_15 = v_14;
    W::Field::add_assign(&mut v_15, &v_1);
    let mut v_16 = v_15;
    W::Field::add_assign_product(&mut v_16, &v_12, &v_2);
    witness_proxy.set_scratch_place(1usize, v_16);
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
    let v_0 = witness_proxy.get_witness_place(7usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(2usize, v_2);
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
    let v_0 = witness_proxy.get_scratch_place(1usize);
    let v_1 = witness_proxy.get_scratch_place(2usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let mut v_3 = v_2;
    W::Field::add_assign_product(&mut v_3, &v_0, &v_1);
    witness_proxy.set_scratch_place(3usize, v_3);
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
    let v_0 = witness_proxy.get_memory_place(9usize);
    let v_1 = witness_proxy.get_memory_place(10usize);
    let v_2 = witness_proxy.get_memory_place(22usize);
    let v_3 = witness_proxy.get_witness_place(4usize);
    let v_4 = witness_proxy.get_witness_place(9usize);
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
    witness_proxy.set_scratch_place(4usize, v_11);
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
    let v_0 = witness_proxy.get_scratch_place(4usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(5usize, v_2);
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
    let v_0 = witness_proxy.get_memory_place(11usize);
    let v_1 = witness_proxy.get_memory_place(12usize);
    let v_2 = witness_proxy.get_memory_place(23usize);
    let v_3 = witness_proxy.get_witness_place(4usize);
    let v_4 = witness_proxy.get_witness_place(9usize);
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
    witness_proxy.set_scratch_place(6usize, v_11);
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
    let v_0 = witness_proxy.get_scratch_place(6usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(7usize, v_2);
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
    let v_0 = witness_proxy.get_memory_place(24usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(8usize, v_2);
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
    let v_0 = witness_proxy.get_witness_place(8usize);
    let v_1 = W::Field::constant(BabyBearField(0u32));
    let mut v_2 = v_1;
    W::Field::add_assign(&mut v_2, &v_0);
    witness_proxy.set_scratch_place(9usize, v_2);
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
    let v_0 = witness_proxy.get_scratch_place(8usize);
    let v_1 = witness_proxy.get_scratch_place(9usize);
    let v_2 = W::Field::constant(BabyBearField(0u32));
    let v_3 = W::Field::constant(BabyBearField(1073741752u32));
    let mut v_4 = v_0;
    W::Field::mul_assign(&mut v_4, &v_3);
    let mut v_5 = v_2;
    W::Field::add_assign_product(&mut v_5, &v_4, &v_1);
    witness_proxy.set_scratch_place(10usize, v_5);
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
    let v_0 = witness_proxy.get_scratch_place(3usize);
    let v_1 = witness_proxy.get_scratch_place(5usize);
    let v_2 = witness_proxy.get_scratch_place(7usize);
    let v_3 = witness_proxy.get_scratch_place_u16(10usize);
    let v_4 = witness_proxy.lookup_enforce::<3usize>(&[v_0, v_1, v_2], v_3, 0usize);
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
}
