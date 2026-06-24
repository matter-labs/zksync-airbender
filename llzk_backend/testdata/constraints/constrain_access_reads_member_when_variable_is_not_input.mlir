module attributes {llzk.lang} {
  struct.def @constraint_test {
    struct.member @member_0 : !felt.type<"mersenne31"> {column}
    function.def @compute() -> !struct.type<@constraint_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@constraint_test<[]>>
      function.return %self : !struct.type<@constraint_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@constraint_test<[]>>) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %0 = struct.readm %arg0[@member_0] : <@constraint_test<[]>>, !felt.type<"mersenne31">
      function.return
    }
  }
}
