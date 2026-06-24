module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_4 = felt.const  4 : <"mersenne31">
      %felt_const_2 = felt.const  2 : <"mersenne31">
      %felt_const_16384 = felt.const  16384 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %true = arith.constant true
      %felt_const_65536 = felt.const  65536 : <"mersenne31">
      %nondet = llzk.nondet : !felt.type<"mersenne31">
      %nondet_0 = llzk.nondet : !felt.type<"mersenne31">
      %0 = bool.cmp lt(%arg1, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %0, %true : i1, i1
      %1 = bool.cmp lt(%arg3, %felt_const_65536) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %1, %true : i1, i1
      %2 = felt.sub %nondet, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = felt.mul %nondet, %2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %3, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %4 = felt.sub %arg2, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = felt.mul %arg2, %4 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %5, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = bool.cmp lt(%nondet_0, %felt_const_16384) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %6, %true : i1, i1
      %7 = felt.mul %felt_const_2, %arg2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %8 = felt.add %7, %nondet : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %9 = felt.add %arg3, %8 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg1, %9 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %10 = felt.mul %felt_const_4, %nondet_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg3, %10 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
