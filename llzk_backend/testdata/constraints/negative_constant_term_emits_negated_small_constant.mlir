module attributes {llzk.lang} {
  struct.def @constraint_test {
    function.def @compute() -> !struct.type<@constraint_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@constraint_test<[]>>
      function.return %self : !struct.type<@constraint_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@constraint_test<[]>>) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %0 = felt.neg %felt_const_1 : !felt.type<"mersenne31">
      function.return
    }
  }
}
