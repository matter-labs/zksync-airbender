module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">, %arg4: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_65536 = felt.const  65536 : <"mersenne31">
      %true = arith.constant true
      %felt_const_2097152 = felt.const  2097152 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %0 = felt.sub %arg1, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %1 = felt.mul %arg1, %0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %1, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.sub %arg1, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = felt.mul %arg1, %2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %3, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %4 = felt.mul %arg1, %arg2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = felt.mul %arg1, %arg3 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = felt.mul %arg1, %arg4 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %7 = bool.cmp lt(%4, %felt_const_2097152) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %7, %true : i1, i1
      %8 = bool.cmp lt(%5, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %8, %true : i1, i1
      %9 = bool.cmp lt(%6, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %9, %true : i1, i1
      function.return
    }
  }
}
