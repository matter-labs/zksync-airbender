module attributes {llzk.lang} {
  struct.def @lookup_test {
    function.def @compute(%arg0: !felt.type<"mersenne31">, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">) -> !struct.type<@lookup_test<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
      %self = struct.new : <@lookup_test<[]>>
      function.return %self : !struct.type<@lookup_test<[]>>
    }
    function.def @constrain(%arg0: !struct.type<@lookup_test<[]>>, %arg1: !felt.type<"mersenne31">, %arg2: !felt.type<"mersenne31">, %arg3: !felt.type<"mersenne31">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
      %felt_const_7 = felt.const  7 : <"mersenne31">
      %felt_const_6 = felt.const  6 : <"mersenne31">
      %felt_const_5 = felt.const  5 : <"mersenne31">
      %felt_const_3 = felt.const  3 : <"mersenne31">
      %felt_const_4 = felt.const  4 : <"mersenne31">
      %felt_const_2 = felt.const  2 : <"mersenne31">
      %felt_const_1 = felt.const  1 : <"mersenne31">
      %felt_const_0 = felt.const  0 : <"mersenne31">
      %felt_const_8 = felt.const  8 : <"mersenne31">
      %true = arith.constant true
      %felt_const_16 = felt.const  16 : <"mersenne31">
      %nondet = llzk.nondet : !felt.type<"mersenne31">
      %nondet_0 = llzk.nondet : !felt.type<"mersenne31">
      %nondet_1 = llzk.nondet : !felt.type<"mersenne31">
      %nondet_2 = llzk.nondet : !felt.type<"mersenne31">
      %0 = bool.cmp lt(%arg1, %felt_const_16) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %0, %true : i1, i1
      %1 = bool.cmp lt(%arg2, %felt_const_8) : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %1, %true : i1, i1
      %2 = felt.sub %nondet, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %3 = felt.mul %nondet, %2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %3, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %4 = felt.sub %nondet_0, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %5 = felt.mul %nondet_0, %4 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %5, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %6 = felt.sub %nondet_1, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %7 = felt.mul %nondet_1, %6 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %7, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %8 = felt.sub %nondet_2, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %9 = felt.mul %nondet_2, %8 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %9, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %10 = felt.sub %arg3, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %11 = felt.mul %arg3, %10 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %11, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %12 = felt.mul %felt_const_2, %nondet_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %13 = felt.mul %felt_const_4, %nondet_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %14 = felt.mul %felt_const_8, %nondet_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %15 = felt.add %nondet, %12 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %16 = felt.add %15, %13 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %17 = felt.add %16, %14 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg1, %17 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %18 = felt.mul %felt_const_2, %nondet_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %19 = felt.mul %18, %nondet_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %20 = felt.neg %19 : !felt.type<"mersenne31">
      %21 = felt.add %nondet_1, %nondet_2 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %22 = felt.add %21, %20 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %23 = felt.mul %nondet_1, %22 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %24 = felt.sub %felt_const_1, %22 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %25 = felt.mul %nondet, %24 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %26 = felt.add %23, %25 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %nondet_3 = llzk.nondet : !felt.type<"mersenne31">
      %27 = felt.sub %nondet_3, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %28 = felt.mul %nondet_3, %27 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %28, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %nondet_4 = llzk.nondet : !felt.type<"mersenne31">
      %29 = felt.sub %nondet_4, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %30 = felt.mul %nondet_4, %29 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %30, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %nondet_5 = llzk.nondet : !felt.type<"mersenne31">
      %31 = felt.sub %nondet_5, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %32 = felt.mul %nondet_5, %31 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %32, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %nondet_6 = llzk.nondet : !felt.type<"mersenne31">
      %33 = felt.sub %nondet_6, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %34 = felt.mul %nondet_6, %33 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %34, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %nondet_7 = llzk.nondet : !felt.type<"mersenne31">
      %35 = felt.sub %nondet_7, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %36 = felt.mul %nondet_7, %35 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %36, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %nondet_8 = llzk.nondet : !felt.type<"mersenne31">
      %37 = felt.sub %nondet_8, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %38 = felt.mul %nondet_8, %37 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %38, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %nondet_9 = llzk.nondet : !felt.type<"mersenne31">
      %39 = felt.sub %nondet_9, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %40 = felt.mul %nondet_9, %39 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %40, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %nondet_10 = llzk.nondet : !felt.type<"mersenne31">
      %41 = felt.sub %nondet_10, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %42 = felt.mul %nondet_10, %41 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %42, %felt_const_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %43 = felt.add %nondet_3, %nondet_4 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %44 = felt.add %43, %nondet_5 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %45 = felt.add %44, %nondet_6 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %46 = felt.add %45, %nondet_7 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %47 = felt.add %46, %nondet_8 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %48 = felt.add %47, %nondet_9 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %49 = felt.add %48, %nondet_10 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %49, %felt_const_1 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %50 = felt.mul %felt_const_1, %nondet_4 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %51 = felt.add %nondet_3, %50 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %52 = felt.mul %felt_const_2, %nondet_5 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %53 = felt.add %51, %52 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %54 = felt.mul %felt_const_3, %nondet_6 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %55 = felt.add %53, %54 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %56 = felt.mul %felt_const_4, %nondet_7 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %57 = felt.add %55, %56 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %58 = felt.mul %felt_const_5, %nondet_8 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %59 = felt.add %57, %58 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %60 = felt.mul %felt_const_6, %nondet_9 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %61 = felt.add %59, %60 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %62 = felt.mul %felt_const_7, %nondet_10 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %63 = felt.add %61, %62 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg2, %63 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %64 = felt.mul %nondet_3, %nondet_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %65 = felt.sub %felt_const_1, %nondet_0 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %66 = felt.mul %nondet_4, %65 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %67 = felt.mul %nondet_5, %26 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %68 = felt.mul %nondet_6, %nondet : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %69 = felt.mul %nondet_7, %26 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %70 = felt.sub %felt_const_1, %26 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %71 = felt.mul %nondet_8, %70 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %72 = felt.mul %nondet_9, %nondet : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %73 = felt.sub %felt_const_1, %nondet : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %74 = felt.mul %nondet_10, %73 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %75 = felt.add %64, %66 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %76 = felt.add %75, %67 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %77 = felt.add %76, %68 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %78 = felt.add %77, %69 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %79 = felt.add %78, %71 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %80 = felt.add %79, %72 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      %81 = felt.add %80, %74 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      constrain.eq %arg3, %81 : !felt.type<"mersenne31">, !felt.type<"mersenne31">
      function.return
    }
  }
}
