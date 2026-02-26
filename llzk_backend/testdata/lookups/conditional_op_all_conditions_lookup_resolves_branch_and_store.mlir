module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %true = arith.constant true
      %felt_const_128 = felt.const  128 : <"mersenne31">
      %felt_const_7 = felt.const  7 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %false = arith.constant false
      %felt_const_6 = felt.const  6 : <"mersenne31">
      %felt_const_5 = felt.const  5 : <"mersenne31">
      %felt_const_4 = felt.const  4 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %felt_const_2 = felt.const  2 : <"mersenne31">
      %felt_const_3 = felt.const  3 : <"mersenne31">
      %felt_const_8 = felt.const  8 : <"mersenne31">
      %0 = felt.umod %arg1, %felt_const_8 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %1 = felt.shr %arg1, %felt_const_3 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.umod %1, %felt_const_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = bool.cmp ne(%2, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %4 = felt.shr %arg1, %felt_const_4 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = felt.umod %4, %felt_const_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = bool.cmp ne(%5, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %7 = felt.shr %arg1, %felt_const_5 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %8 = felt.umod %7, %felt_const_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %9 = bool.cmp ne(%8, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %10 = felt.shr %arg1, %felt_const_6 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %11 = felt.umod %10, %felt_const_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %12 = bool.cmp ne(%11, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %13 = bool.not %12 : i1
      %14 = bool.and %9, %13 : i1, i1
      %15 = bool.not %9 : i1
      %16 = bool.and %15, %12 : i1, i1
      %17 = bool.or %14, %16 : i1, i1
      %18 = arith.select %17, %9, %3 : i1
      %19 = bool.cmp eq(%0, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %20 = bool.cmp eq(%0, %felt_const_1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %21 = bool.not %6 : i1
      %22 = bool.cmp eq(%0, %felt_const_4) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %23 = bool.cmp eq(%0, %felt_const_5) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %24 = bool.not %18 : i1
      %25 = bool.cmp eq(%0, %felt_const_6) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %26 = bool.cmp eq(%0, %felt_const_7) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %27 = bool.not %3 : i1
      %28 = arith.select %26, %27, %false : i1
      %29 = arith.select %25, %3, %28 : i1
      %30 = arith.select %23, %24, %29 : i1
      %31 = arith.select %22, %18, %30 : i1
      %32 = arith.select %20, %21, %31 : i1
      %33 = arith.select %19, %6, %32 : i1
      %34 = bool.cmp eq(%0, %felt_const_2) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %35 = bool.cmp eq(%0, %felt_const_3) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %36 = arith.select %35, %3, %false : i1
      %37 = arith.select %34, %18, %36 : i1
      %38 = arith.select %33, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %39 = arith.select %37, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %40 = bool.cmp lt(%arg1, %felt_const_128) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %40, %true : i1, i1
      %41 = felt.sub %arg2, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %42 = felt.mul %arg2, %41 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %42, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %43 = felt.sub %arg3, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %44 = felt.mul %arg3, %43 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %44, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg2, %38 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg3, %39 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
