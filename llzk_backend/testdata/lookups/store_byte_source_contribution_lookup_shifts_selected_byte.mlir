module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_8 = felt.const  8 : <"mersenne31">
      %felt_const_65536 = felt.const  65536 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %true = arith.constant true
      %felt_const_256 = felt.const  256 : <"mersenne31">
      %0 = bool.cmp lt(%arg1, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %0, %true : i1, i1
      %1 = felt.sub %arg2, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.mul %arg2, %1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %2, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = bool.cmp lt(%arg3, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %3, %true : i1, i1
      %4 = felt.shl %arg1, %felt_const_8 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = bool.cmp ne(%arg2, %felt_const_0) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = arith.select %5, %4, %arg1 : !felt.type<"mersenne31">
      constrain.eq %arg3, %6 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
