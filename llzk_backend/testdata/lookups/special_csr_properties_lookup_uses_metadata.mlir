module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_7 = felt.const  7 : <"mersenne31">
      %felt_const_5 = felt.const  5 : <"mersenne31">
      %felt_const_9 = felt.const  9 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %true = arith.constant true
      %felt_const_4096 = felt.const  4096 : <"mersenne31">
      %0 = bool.cmp lt(%arg1, %felt_const_4096) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %0, %true : i1, i1
      %1 = felt.sub %arg2, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.mul %arg2, %1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %2, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = felt.sub %arg3, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %4 = felt.mul %arg3, %3 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %4, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = bool.cmp eq(%arg1, %felt_const_9) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = arith.select %5, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %7 = bool.cmp eq(%arg1, %felt_const_5) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %8 = arith.select %7, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %9 = bool.cmp eq(%arg1, %felt_const_7) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %10 = arith.select %9, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %11 = felt.add %8, %10 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %12 = felt.add %11, %6 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg3, %6 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg2, %12 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
