module attributes {llzk.lang} {
  struct.def @constraint_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">) -> !struct.type<@constraint_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@constraint_test<[]>>
      function.return %self : !struct.type<@constraint_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@constraint_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_4 = felt.const  4 : <"mersenne31">
      %felt_const_3 = felt.const  3 : <"mersenne31">
      %felt_const_5 = felt.const  5 : <"mersenne31">
      %0 = felt.mul %felt_const_3, %arg1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %1 = felt.add %felt_const_5, %0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.mul %felt_const_4, %arg2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = felt.add %1, %2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
