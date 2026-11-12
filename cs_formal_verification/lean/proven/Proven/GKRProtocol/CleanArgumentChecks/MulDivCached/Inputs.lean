module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanLookupArgumentsImport
public import Proven.Import.GKRProtocol.CleanHelperArgumentsImport
public import Proven.Import.GKRProtocol.CleanGenericArgumentsImport
public import Proven.GKRProtocol.CleanArithmeticNative.MulDivCached
public import Proven.GKRProtocol.FunctionalLinksNative.MulDivCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArgumentsNative.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

import_clean_lookup_arguments native from "artifacts/compiler/mul-div-cached.json"
  certificate "artifacts/compiler/lookup/mul-div-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivCached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivCached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivCached.native phase 0

import_clean_helper_arguments native from "artifacts/compiler/mul-div-cached.json"
  helper_indices "{\"format_version\":1,\"addresses\":[{\"BaseLayerMemory\":18},{\"BaseLayerMemory\":19},{\"BaseLayerMemory\":20},{\"BaseLayerMemory\":21},{\"BaseLayerMemory\":17},{\"BaseLayerMemory\":4},{\"BaseLayerMemory\":9},{\"BaseLayerMemory\":14},{\"BaseLayerWitness\":0},{\"BaseLayerWitness\":1},{\"BaseLayerWitness\":2},{\"BaseLayerWitness\":3},{\"BaseLayerWitness\":4},{\"BaseLayerWitness\":5},{\"BaseLayerMemory\":22},{\"BaseLayerMemory\":23},{\"BaseLayerMemory\":24},{\"BaseLayerMemory\":25},{\"BaseLayerMemory\":0},{\"BaseLayerMemory\":1},{\"BaseLayerMemory\":2},{\"BaseLayerMemory\":3},{\"BaseLayerMemory\":5},{\"BaseLayerMemory\":6},{\"BaseLayerMemory\":7},{\"BaseLayerMemory\":8},{\"BaseLayerMemory\":12},{\"BaseLayerMemory\":13},{\"BaseLayerMemory\":15},{\"BaseLayerMemory\":16},{\"BaseLayerMemory\":10},{\"BaseLayerMemory\":11},{\"BaseLayerWitness\":6},{\"BaseLayerWitness\":7},{\"BaseLayerWitness\":8},{\"BaseLayerWitness\":9},{\"BaseLayerWitness\":10},{\"BaseLayerWitness\":11},{\"BaseLayerWitness\":12},{\"BaseLayerWitness\":13},{\"BaseLayerWitness\":14},{\"BaseLayerWitness\":15},{\"BaseLayerWitness\":16},{\"BaseLayerWitness\":17},{\"InnerLayer\":{\"layer\":1,\"offset\":5}},{\"InnerLayer\":{\"layer\":1,\"offset\":6}},{\"InnerLayer\":{\"layer\":1,\"offset\":7}},{\"InnerLayer\":{\"layer\":1,\"offset\":8}},{\"InnerLayer\":{\"layer\":1,\"offset\":9}},{\"InnerLayer\":{\"layer\":1,\"offset\":10}},{\"InnerLayer\":{\"layer\":1,\"offset\":11}},{\"InnerLayer\":{\"layer\":1,\"offset\":12}},{\"InnerLayer\":{\"layer\":1,\"offset\":13}},{\"InnerLayer\":{\"layer\":1,\"offset\":14}},{\"InnerLayer\":{\"layer\":1,\"offset\":15}},{\"InnerLayer\":{\"layer\":1,\"offset\":16}},{\"InnerLayer\":{\"layer\":1,\"offset\":17}},{\"InnerLayer\":{\"layer\":1,\"offset\":18}},{\"InnerLayer\":{\"layer\":1,\"offset\":19}},{\"InnerLayer\":{\"layer\":1,\"offset\":20}},{\"InnerLayer\":{\"layer\":1,\"offset\":21}},{\"InnerLayer\":{\"layer\":1,\"offset\":22}},{\"InnerLayer\":{\"layer\":1,\"offset\":23}},{\"InnerLayer\":{\"layer\":1,\"offset\":24}},{\"InnerLayer\":{\"layer\":1,\"offset\":25}},{\"BaseLayerWitness\":18},{\"BaseLayerWitness\":19},{\"BaseLayerWitness\":20},{\"BaseLayerWitness\":21},{\"BaseLayerWitness\":22},{\"BaseLayerWitness\":23},{\"InnerLayer\":{\"layer\":1,\"offset\":0}},{\"InnerLayer\":{\"layer\":1,\"offset\":34}},{\"Cached\":{\"layer\":0,\"offset\":13}},{\"InnerLayer\":{\"layer\":1,\"offset\":43}},{\"InnerLayer\":{\"layer\":2,\"offset\":0}},{\"VirtualSetup\":\"InitsAndTeardownsLow\"},{\"VirtualSetup\":\"InitsAndTeardownsHigh\"}],\"operands\":[{\"native_leaf\":8,\"locator\":[31,0],\"expansion\":[],\"source_index\":0,\"witness\":[]},{\"native_leaf\":10,\"locator\":[32,0],\"expansion\":[],\"source_index\":1,\"witness\":[]},{\"native_leaf\":11,\"locator\":[32,1],\"expansion\":[8],\"source_index\":2,\"witness\":[]},{\"native_leaf\":12,\"locator\":[33,0],\"expansion\":[9],\"source_index\":3,\"witness\":[]},{\"native_leaf\":13,\"locator\":[33,1],\"expansion\":[10],\"source_index\":4,\"witness\":[]},{\"native_leaf\":14,\"locator\":[34,0],\"expansion\":[11],\"source_index\":5,\"witness\":[]},{\"native_leaf\":15,\"locator\":[34,1],\"expansion\":[12],\"source_index\":6,\"witness\":[]},{\"native_leaf\":25,\"locator\":[59,0],\"expansion\":[35,13],\"source_index\":7,\"witness\":[]}],\"setup_leaf\":9,\"group\":{\"native_leaves\":[14,15,25,8,9,12,13,10,11],\"source_labels\":[5,6,7,0,8,3,4,1,2]}}"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivCached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  helper_model Airbender.Compiler.HelperNative.MulDivCached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivCached.native phase 0

end Airbender.Compiler.CleanArgumentsNative.MulDivCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/mul-div-cached.json"
  certificate "artifacts/compiler/lookup/mul-div-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivCached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivCached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivCached.native
  start 0 stop 8 part_size 8 phase 0

namespace native

noncomputable def genericExpressions0 : Vector (Airbender.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression0_0, part0.genericExpression0_1, part0.genericExpression0_2, part0.genericExpression0_3, part0.genericExpression0_4, part0.genericExpression0_5, part0.genericExpression0_6, part0.genericExpression0_7, part0.genericExpression0_8]

noncomputable def genericExpressions1 : Vector (Airbender.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression1_0, part0.genericExpression1_1, part0.genericExpression1_2, part0.genericExpression1_3, part0.genericExpression1_4, part0.genericExpression1_5, part0.genericExpression1_6, part0.genericExpression1_7, part0.genericExpression1_8]

noncomputable def genericExpressions2 : Vector (Airbender.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression2_0, part0.genericExpression2_1, part0.genericExpression2_2, part0.genericExpression2_3, part0.genericExpression2_4, part0.genericExpression2_5, part0.genericExpression2_6, part0.genericExpression2_7, part0.genericExpression2_8]

noncomputable def genericExpressions3 : Vector (Airbender.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression3_0, part0.genericExpression3_1, part0.genericExpression3_2, part0.genericExpression3_3, part0.genericExpression3_4, part0.genericExpression3_5, part0.genericExpression3_6, part0.genericExpression3_7, part0.genericExpression3_8]

noncomputable def genericExpressions4 : Vector (Airbender.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression4_0, part0.genericExpression4_1, part0.genericExpression4_2, part0.genericExpression4_3, part0.genericExpression4_4, part0.genericExpression4_5, part0.genericExpression4_6, part0.genericExpression4_7, part0.genericExpression4_8]

noncomputable def genericExpressions5 : Vector (Airbender.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression5_0, part0.genericExpression5_1, part0.genericExpression5_2, part0.genericExpression5_3, part0.genericExpression5_4, part0.genericExpression5_5, part0.genericExpression5_6, part0.genericExpression5_7, part0.genericExpression5_8]

noncomputable def genericExpressions6 : Vector (Airbender.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression6_0, part0.genericExpression6_1, part0.genericExpression6_2, part0.genericExpression6_3, part0.genericExpression6_4, part0.genericExpression6_5, part0.genericExpression6_6, part0.genericExpression6_7, part0.genericExpression6_8]

noncomputable def genericExpressions7 : Vector (Airbender.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression7_0, part0.genericExpression7_1, part0.genericExpression7_2, part0.genericExpression7_3, part0.genericExpression7_4, part0.genericExpression7_5, part0.genericExpression7_6, part0.genericExpression7_7, part0.genericExpression7_8]

noncomputable def genericExpressions : List (Vector (Airbender.Expression Source.BaseField) 9) :=
  [genericExpressions0, genericExpressions1, genericExpressions2, genericExpressions3, genericExpressions4, genericExpressions5, genericExpressions6, genericExpressions7]

end native

end Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached
