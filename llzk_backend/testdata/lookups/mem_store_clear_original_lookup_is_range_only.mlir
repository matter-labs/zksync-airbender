module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_65536 = felt.const  65536 : <"mersenne31">
      %true = arith.constant true
      %felt_const_2097152 = felt.const  2097152 : <"mersenne31">
      %0 = bool.cmp lt(%arg1, %felt_const_2097152) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %0, %true : i1, i1
      %1 = bool.cmp lt(%arg2, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %1, %true : i1, i1
      %2 = bool.cmp lt(%arg3, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %2, %true : i1, i1
      function.return
    }
  }
}
