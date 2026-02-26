module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">, %arg4: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %true = arith.constant true
      %felt_const_256 = felt.const  256 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %felt_const_7 = felt.const  7 : <"mersenne31">
      %felt_const_6 = felt.const  6 : <"mersenne31">
      %felt_const_4 = felt.const  4 : <"mersenne31">
      %0 = bool.cmp eq(%arg1, %felt_const_4) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %1 = bool.cmp eq(%arg1, %felt_const_6) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %2 = bool.cmp eq(%arg1, %felt_const_7) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = arith.select %0, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %4 = felt.sub %3, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = felt.mul %3, %4 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %5, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = arith.select %1, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %7 = felt.sub %6, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %8 = felt.mul %6, %7 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %8, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %9 = arith.select %2, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %10 = felt.sub %9, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %11 = felt.mul %9, %10 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %11, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %12 = arith.select %0, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %13 = arith.select %1, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %14 = arith.select %2, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %15 = felt.add %12, %13 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %16 = felt.add %15, %14 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %16, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %17 = arith.select %0, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %18 = bool.cmp lt(%arg2, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %19 = bool.cmp eq(%felt_const_0, %17) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %20 = arith.cmpi eq, %18, %true : i1
      %21 = bool.or %19, %20 : i1, i1
      constrain.eq %21, %true : i1, i1
      %22 = bool.cmp lt(%arg3, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %23 = bool.cmp eq(%felt_const_0, %17) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %24 = arith.cmpi eq, %22, %true : i1
      %25 = bool.or %23, %24 : i1, i1
      constrain.eq %25, %true : i1, i1
      %26 = bool.cmp lt(%arg4, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %27 = bool.cmp eq(%felt_const_0, %17) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %28 = arith.cmpi eq, %26, %true : i1
      %29 = bool.or %27, %28 : i1, i1
      constrain.eq %29, %true : i1, i1
      %30 = felt.bit_xor %arg2, %arg3 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %31 = bool.cmp eq(%felt_const_0, %17) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %32 = bool.cmp eq(%arg4, %30) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %33 = bool.or %31, %32 : i1, i1
      constrain.eq %33, %true : i1, i1
      %34 = arith.select %1, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %35 = bool.cmp lt(%arg2, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %36 = bool.cmp eq(%felt_const_0, %34) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %37 = arith.cmpi eq, %35, %true : i1
      %38 = bool.or %36, %37 : i1, i1
      constrain.eq %38, %true : i1, i1
      %39 = bool.cmp lt(%arg3, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %40 = bool.cmp eq(%felt_const_0, %34) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %41 = arith.cmpi eq, %39, %true : i1
      %42 = bool.or %40, %41 : i1, i1
      constrain.eq %42, %true : i1, i1
      %43 = bool.cmp lt(%arg4, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %44 = bool.cmp eq(%felt_const_0, %34) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %45 = arith.cmpi eq, %43, %true : i1
      %46 = bool.or %44, %45 : i1, i1
      constrain.eq %46, %true : i1, i1
      %47 = felt.bit_or %arg2, %arg3 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %48 = bool.cmp eq(%felt_const_0, %34) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %49 = bool.cmp eq(%arg4, %47) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %50 = bool.or %48, %49 : i1, i1
      constrain.eq %50, %true : i1, i1
      %51 = arith.select %2, %felt_const_1, %felt_const_0 : !felt.type<"mersenne31">
      %52 = bool.cmp lt(%arg2, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %53 = bool.cmp eq(%felt_const_0, %51) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %54 = arith.cmpi eq, %52, %true : i1
      %55 = bool.or %53, %54 : i1, i1
      constrain.eq %55, %true : i1, i1
      %56 = bool.cmp lt(%arg3, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %57 = bool.cmp eq(%felt_const_0, %51) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %58 = arith.cmpi eq, %56, %true : i1
      %59 = bool.or %57, %58 : i1, i1
      constrain.eq %59, %true : i1, i1
      %60 = bool.cmp lt(%arg4, %felt_const_256) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %61 = bool.cmp eq(%felt_const_0, %51) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %62 = arith.cmpi eq, %60, %true : i1
      %63 = bool.or %61, %62 : i1, i1
      constrain.eq %63, %true : i1, i1
      %64 = felt.bit_and %arg2, %arg3 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %65 = bool.cmp eq(%felt_const_0, %51) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %66 = bool.cmp eq(%arg4, %64) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %67 = bool.or %65, %66 : i1, i1
      constrain.eq %67, %true : i1, i1
      function.return
    }
  }
}
