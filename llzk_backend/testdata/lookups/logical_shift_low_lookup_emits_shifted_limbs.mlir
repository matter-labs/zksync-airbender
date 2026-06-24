module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %true = arith.constant true
      %felt_const_2097152 = felt.const  2097152 : <"mersenne31">
      %felt_const_32 = felt.const  32 : <"mersenne31">
      %felt_const_16 = felt.const  16 : <"mersenne31">
      %felt_const_65536 = felt.const  65536 : <"mersenne31">
      %0 = felt.umod %arg1, %felt_const_65536 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %1 = felt.shr %arg1, %felt_const_16 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.umod %1, %felt_const_32 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = felt.shl %0, %2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %4 = felt.umod %3, %felt_const_65536 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = felt.shr %3, %felt_const_16 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = felt.umod %5, %felt_const_65536 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %7 = bool.cmp lt(%arg1, %felt_const_2097152) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %7, %true : i1, i1
      %8 = bool.cmp lt(%arg2, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %8, %true : i1, i1
      %9 = bool.cmp lt(%arg3, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %9, %true : i1, i1
      constrain.eq %arg2, %4 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg3, %6 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
