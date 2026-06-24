module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">, %arg4: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_4 = felt.const  4 : <"mersenne31">
      %felt_const_2 = felt.const  2 : <"mersenne31">
      %felt_const_16384 = felt.const  16384 : <"mersenne31">
      %true = arith.constant true
      %felt_const_65536 = felt.const  65536 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %0 = felt.sub %arg1, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %1 = felt.mul %arg1, %0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %1, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.sub %arg1, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = felt.mul %arg1, %2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %3, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %nondet = llzk.nondet : !felt.type<"mersenne31">
      %nondet_0 = llzk.nondet : !felt.type<"mersenne31">
      %4 = bool.cmp lt(%arg2, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = bool.cmp eq(%felt_const_0, %arg1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = arith.cmpi eq, %4, %true : i1
      %7 = bool.or %5, %6 : i1, i1
      constrain.eq %7, %true : i1, i1
      %8 = bool.cmp lt(%arg4, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %9 = bool.cmp eq(%felt_const_0, %arg1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %10 = arith.cmpi eq, %8, %true : i1
      %11 = bool.or %9, %10 : i1, i1
      constrain.eq %11, %true : i1, i1
      %12 = felt.sub %nondet, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %13 = felt.mul %nondet, %12 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %14 = bool.cmp eq(%felt_const_0, %arg1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %15 = bool.cmp eq(%13, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %16 = bool.or %14, %15 : i1, i1
      constrain.eq %16, %true : i1, i1
      %17 = felt.sub %arg3, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %18 = felt.mul %arg3, %17 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %19 = bool.cmp eq(%felt_const_0, %arg1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %20 = bool.cmp eq(%18, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %21 = bool.or %19, %20 : i1, i1
      constrain.eq %21, %true : i1, i1
      %22 = bool.cmp lt(%nondet_0, %felt_const_16384) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %23 = bool.cmp eq(%felt_const_0, %arg1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %24 = arith.cmpi eq, %22, %true : i1
      %25 = bool.or %23, %24 : i1, i1
      constrain.eq %25, %true : i1, i1
      %26 = felt.mul %felt_const_2, %arg3 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %27 = felt.add %26, %nondet : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %28 = felt.add %arg4, %27 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %29 = bool.cmp eq(%felt_const_0, %arg1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %30 = bool.cmp eq(%arg2, %28) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %31 = bool.or %29, %30 : i1, i1
      constrain.eq %31, %true : i1, i1
      %32 = felt.mul %felt_const_4, %nondet_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %33 = bool.cmp eq(%felt_const_0, %arg1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %34 = bool.cmp eq(%arg4, %32) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %35 = bool.or %33, %34 : i1, i1
      constrain.eq %35, %true : i1, i1
      function.return
    }
  }
}
