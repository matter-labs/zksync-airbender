module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_1024 = felt.const  1024 : <"mersenne31">
      %felt_const_64 = felt.const  64 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %true = arith.constant true
      %felt_const_65536 = felt.const  65536 : <"mersenne31">
      %nondet = llzk.nondet : !felt.type<"mersenne31">
      %nondet_0 = llzk.nondet : !felt.type<"mersenne31">
      %0 = bool.cmp lt(%arg1, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %0, %true : i1, i1
      %1 = felt.sub %arg2, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = felt.mul %arg2, %1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %2, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = bool.cmp lt(%arg3, %felt_const_64) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %3, %true : i1, i1
      %4 = bool.cmp lt(%nondet, %felt_const_1024) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %4, %true : i1, i1
      %5 = bool.cmp lt(%nondet, %felt_const_1024) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %5, %true : i1, i1
      %6 = felt.mul %felt_const_64, %nondet_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %7 = felt.add %arg3, %6 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg1, %7 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %8 = felt.add %felt_const_1, %nondet : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %9 = felt.mul %arg2, %8 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %nondet_0, %9 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
