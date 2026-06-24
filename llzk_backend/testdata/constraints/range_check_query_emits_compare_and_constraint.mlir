module attributes {llzk.lang} {
  struct.def @constraint_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">) -> !struct.type<@constraint_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@constraint_test<[]>>
      function.return %self : !struct.type<@constraint_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@constraint_test<[]>>, %arg1: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %true = arith.constant true
      %felt_const_256 = felt.const  256 : <"mersenne31">
      %0 = bool.cmp lt(%arg1, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %0, %true : i1, i1
      function.return
    }
  }
}
