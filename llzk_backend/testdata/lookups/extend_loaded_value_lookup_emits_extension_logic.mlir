module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %true = arith.constant true
      %felt_const_1048576 = felt.const  1048576 : <"mersenne31">
      %felt_const_5 = felt.const  5 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %felt_const_4 = felt.const  4 : <"mersenne31">
      %felt_const_65280 = felt.const  65280 : <"mersenne31">
      %felt_const_65535 = felt.const  65535 : <"mersenne31">
      %felt_const_15 = felt.const  15 : <"mersenne31">
      %felt_const_7 = felt.const  7 : <"mersenne31">
      %felt_const_256 = felt.const  256 : <"mersenne31">
      %felt_const_8 = felt.const  8 : <"mersenne31">
      %felt_const_17 = felt.const  17 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %felt_const_2 = felt.const  2 : <"mersenne31">
      %felt_const_16 = felt.const  16 : <"mersenne31">
      %felt_const_65536 = felt.const  65536 : <"mersenne31">
      %0 = felt.umod %arg1, %felt_const_65536 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %1 = felt.shr %arg1, %felt_const_16 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.umod %1, %felt_const_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = bool.cmp ne(%2, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %4 = felt.shr %arg1, %felt_const_17 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = felt.umod %4, %felt_const_8 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = felt.umod %0, %felt_const_256 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %7 = felt.shr %0, %felt_const_8 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %8 = felt.umod %7, %felt_const_256 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %9 = arith.select %3, %8, %6 : !felt.type<"mersenne31">
      %10 = felt.shr %9, %felt_const_7 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %11 = felt.umod %10, %felt_const_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %12 = bool.cmp ne(%11, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %13 = felt.shr %0, %felt_const_15 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %14 = felt.umod %13, %felt_const_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %15 = bool.cmp ne(%14, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %16 = bool.cmp eq(%5, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %17 = felt.add %9, %felt_const_65280 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %18 = arith.select %12, %17, %9 : !felt.type<"mersenne31">
      %19 = bool.cmp eq(%5, %felt_const_4) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %20 = bool.cmp eq(%5, %felt_const_1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %21 = bool.cmp eq(%5, %felt_const_5) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %22 = arith.select %21, %0, %felt_const_0 : !felt.type<"mersenne31">
      %23 = arith.select %20, %0, %22 : !felt.type<"mersenne31">
      %24 = arith.select %19, %9, %23 : !felt.type<"mersenne31">
      %25 = arith.select %16, %18, %24 : !felt.type<"mersenne31">
      %26 = bool.cmp eq(%5, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %27 = arith.select %12, %felt_const_65535, %felt_const_0 : !felt.type<"mersenne31">
      %28 = bool.cmp eq(%5, %felt_const_1) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %29 = arith.select %15, %felt_const_65535, %felt_const_0 : !felt.type<"mersenne31">
      %30 = arith.select %28, %29, %felt_const_0 : !felt.type<"mersenne31">
      %31 = arith.select %26, %27, %30 : !felt.type<"mersenne31">
      %32 = bool.cmp lt(%arg1, %felt_const_1048576) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %32, %true : i1, i1
      %33 = bool.cmp lt(%arg2, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %33, %true : i1, i1
      %34 = bool.cmp lt(%arg3, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %34, %true : i1, i1
      constrain.eq %arg2, %25 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg3, %31 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
