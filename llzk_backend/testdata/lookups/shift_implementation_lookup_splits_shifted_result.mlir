module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %true = arith.constant true
      %felt_const_4194304 = felt.const  4194304 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %felt_const_2 = felt.const  2 : <"mersenne31">
      %felt_const_21 = felt.const  21 : <"mersenne31">
      %felt_const_32 = felt.const  32 : <"mersenne31">
      %felt_const_16 = felt.const  16 : <"mersenne31">
      %felt_const_65536 = felt.const  65536 : <"mersenne31">
      %0 = felt.umod %arg1, %felt_const_65536 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %1 = felt.shr %arg1, %felt_const_16 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.umod %1, %felt_const_32 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = felt.shr %arg1, %felt_const_21 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %4 = felt.umod %3, %felt_const_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = bool.cmp ne(%4, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = felt.shl %0, %felt_const_16 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %7 = felt.shr %6, %2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %8 = felt.shl %0, %2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %9 = felt.shr %7, %felt_const_16 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %10 = felt.umod %9, %felt_const_65536 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %11 = felt.umod %8, %felt_const_65536 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %12 = arith.select %5, %10, %11 : !felt.type<"mersenne31">
      %13 = felt.umod %7, %felt_const_65536 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %14 = felt.shr %8, %felt_const_16 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %15 = felt.umod %14, %felt_const_65536 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %16 = arith.select %5, %13, %15 : !felt.type<"mersenne31">
      %17 = bool.cmp lt(%arg1, %felt_const_4194304) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %17, %true : i1, i1
      %18 = bool.cmp lt(%arg2, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %18, %true : i1, i1
      %19 = bool.cmp lt(%arg3, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %19, %true : i1, i1
      constrain.eq %arg2, %12 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg3, %16 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
