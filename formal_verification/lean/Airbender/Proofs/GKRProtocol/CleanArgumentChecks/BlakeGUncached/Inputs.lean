import Airbender.Import.GKRProtocol.CleanLookupArgumentsImport
import Airbender.Import.GKRProtocol.CleanHelperArgumentsImport
import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.BlakeGUncached

namespace Airbender.Compiler.CleanArgumentsNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_lookup_arguments native from "artifacts/compiler/blake-g-uncached.json"
  certificate "artifacts/compiler/lookup/blake-g-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeGUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeGUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeGUncached.native phase 0

import_clean_helper_arguments native from "artifacts/compiler/blake-g-uncached.json"
  helper_indices "{\"format_version\":1,\"addresses\":[{\"BaseLayerMemory\":52},{\"BaseLayerMemory\":53},{\"BaseLayerMemory\":54},{\"BaseLayerMemory\":48},{\"BaseLayerMemory\":49},{\"BaseLayerMemory\":50},{\"BaseLayerMemory\":51},{\"BaseLayerMemory\":8},{\"BaseLayerMemory\":15},{\"BaseLayerMemory\":22},{\"BaseLayerMemory\":29},{\"BaseLayerMemory\":40},{\"BaseLayerMemory\":45},{\"BaseLayerMemory\":2},{\"BaseLayerMemory\":3},{\"BaseLayerMemory\":6},{\"BaseLayerMemory\":7},{\"BaseLayerMemory\":9},{\"BaseLayerMemory\":10},{\"BaseLayerMemory\":13},{\"BaseLayerMemory\":14},{\"BaseLayerMemory\":16},{\"BaseLayerMemory\":17},{\"BaseLayerMemory\":20},{\"BaseLayerMemory\":21},{\"BaseLayerMemory\":23},{\"BaseLayerMemory\":24},{\"BaseLayerMemory\":27},{\"BaseLayerMemory\":28},{\"BaseLayerMemory\":30},{\"BaseLayerMemory\":31},{\"BaseLayerMemory\":34},{\"BaseLayerMemory\":35},{\"BaseLayerMemory\":38},{\"BaseLayerMemory\":39},{\"BaseLayerMemory\":43},{\"BaseLayerMemory\":44},{\"BaseLayerWitness\":0},{\"BaseLayerWitness\":1},{\"BaseLayerWitness\":2},{\"BaseLayerWitness\":3},{\"BaseLayerWitness\":4},{\"BaseLayerWitness\":5},{\"BaseLayerWitness\":6},{\"BaseLayerWitness\":7},{\"BaseLayerWitness\":8},{\"BaseLayerWitness\":9},{\"BaseLayerWitness\":10},{\"BaseLayerWitness\":11},{\"BaseLayerWitness\":12},{\"BaseLayerWitness\":13},{\"BaseLayerWitness\":14},{\"BaseLayerWitness\":15},{\"BaseLayerWitness\":16},{\"BaseLayerWitness\":17},{\"BaseLayerWitness\":18},{\"BaseLayerWitness\":19},{\"BaseLayerWitness\":20},{\"BaseLayerWitness\":21},{\"BaseLayerWitness\":22},{\"BaseLayerWitness\":23},{\"BaseLayerWitness\":24},{\"BaseLayerWitness\":25},{\"BaseLayerWitness\":26},{\"BaseLayerWitness\":27},{\"BaseLayerWitness\":28},{\"BaseLayerWitness\":29},{\"BaseLayerWitness\":30},{\"BaseLayerWitness\":31},{\"BaseLayerWitness\":32},{\"BaseLayerWitness\":33},{\"BaseLayerWitness\":34},{\"BaseLayerWitness\":35},{\"BaseLayerWitness\":36},{\"BaseLayerWitness\":37},{\"BaseLayerWitness\":38},{\"BaseLayerWitness\":39},{\"BaseLayerWitness\":40},{\"BaseLayerWitness\":41},{\"BaseLayerWitness\":42},{\"BaseLayerWitness\":43},{\"BaseLayerWitness\":44},{\"BaseLayerWitness\":45},{\"BaseLayerWitness\":46},{\"BaseLayerWitness\":47},{\"BaseLayerWitness\":48},{\"BaseLayerWitness\":49},{\"BaseLayerWitness\":50},{\"BaseLayerWitness\":51},{\"BaseLayerWitness\":52},{\"BaseLayerWitness\":53},{\"BaseLayerWitness\":54},{\"BaseLayerWitness\":55},{\"BaseLayerWitness\":56},{\"BaseLayerMemory\":0},{\"BaseLayerMemory\":1},{\"BaseLayerMemory\":4},{\"BaseLayerMemory\":5},{\"BaseLayerMemory\":11},{\"BaseLayerMemory\":12},{\"BaseLayerMemory\":18},{\"BaseLayerMemory\":19},{\"BaseLayerMemory\":25},{\"BaseLayerMemory\":26},{\"BaseLayerMemory\":32},{\"BaseLayerMemory\":33},{\"BaseLayerMemory\":36},{\"BaseLayerMemory\":37},{\"BaseLayerMemory\":41},{\"BaseLayerMemory\":42},{\"BaseLayerMemory\":46},{\"BaseLayerMemory\":47},{\"InnerLayer\":{\"layer\":1,\"offset\":0}},{\"InnerLayer\":{\"layer\":2,\"offset\":0}},{\"InnerLayer\":{\"layer\":3,\"offset\":0}},{\"InnerLayer\":{\"layer\":4,\"offset\":0}},{\"VirtualSetup\":\"InitsAndTeardownsLow\"},{\"VirtualSetup\":\"InitsAndTeardownsHigh\"}],\"operands\":[{\"native_leaf\":0,\"locator\":[11,0],\"expansion\":[],\"source_index\":0,\"witness\":[]},{\"native_leaf\":2,\"locator\":[12,0],\"expansion\":[],\"source_index\":1,\"witness\":[]},{\"native_leaf\":3,\"locator\":[12,1],\"expansion\":[],\"source_index\":2,\"witness\":[]},{\"native_leaf\":4,\"locator\":[13,0],\"expansion\":[],\"source_index\":3,\"witness\":[]},{\"native_leaf\":5,\"locator\":[13,1],\"expansion\":[],\"source_index\":4,\"witness\":[]},{\"native_leaf\":6,\"locator\":[14,0],\"expansion\":[],\"source_index\":5,\"witness\":[]},{\"native_leaf\":7,\"locator\":[14,1],\"expansion\":[],\"source_index\":6,\"witness\":[]},{\"native_leaf\":8,\"locator\":[15,0],\"expansion\":[],\"source_index\":7,\"witness\":[]},{\"native_leaf\":9,\"locator\":[15,1],\"expansion\":[],\"source_index\":8,\"witness\":[]},{\"native_leaf\":10,\"locator\":[16,0],\"expansion\":[],\"source_index\":9,\"witness\":[]},{\"native_leaf\":11,\"locator\":[16,1],\"expansion\":[],\"source_index\":10,\"witness\":[]},{\"native_leaf\":12,\"locator\":[17,0],\"expansion\":[],\"source_index\":11,\"witness\":[]},{\"native_leaf\":13,\"locator\":[17,1],\"expansion\":[],\"source_index\":12,\"witness\":[]},{\"native_leaf\":14,\"locator\":[18,0],\"expansion\":[],\"source_index\":13,\"witness\":[]},{\"native_leaf\":15,\"locator\":[18,1],\"expansion\":[],\"source_index\":14,\"witness\":[]},{\"native_leaf\":16,\"locator\":[19,0],\"expansion\":[],\"source_index\":15,\"witness\":[]},{\"native_leaf\":17,\"locator\":[19,1],\"expansion\":[],\"source_index\":16,\"witness\":[]},{\"native_leaf\":18,\"locator\":[20,0],\"expansion\":[],\"source_index\":17,\"witness\":[]},{\"native_leaf\":19,\"locator\":[20,1],\"expansion\":[],\"source_index\":18,\"witness\":[]},{\"native_leaf\":20,\"locator\":[21,0],\"expansion\":[],\"source_index\":19,\"witness\":[]},{\"native_leaf\":21,\"locator\":[21,1],\"expansion\":[],\"source_index\":20,\"witness\":[]}],\"setup_leaf\":1,\"group\":{\"native_leaves\":[0,1,4,5,2,3,16,17,14,15,20,21,18,19,8,9,6,7,12,13,10,11],\"source_labels\":[0,21,3,4,1,2,15,16,13,14,19,20,17,18,7,8,5,6,11,12,9,10]}}"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  helper_model Airbender.Compiler.HelperNative.BlakeGUncached.native
  memory_model Airbender.Compiler.MemoryNative.BlakeGUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeGUncached.native phase 0

end Airbender.Compiler.CleanArgumentsNative.BlakeGUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/blake-g-uncached.json"
  certificate "artifacts/compiler/lookup/blake-g-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeGUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeGUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeGUncached.native
  start 0 stop 19 part_size 8 phase 0

namespace native

noncomputable def genericExpressions0 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression0_0, part0.genericExpression0_1, part0.genericExpression0_2, part0.genericExpression0_3, part0.genericExpression0_4, part0.genericExpression0_5, part0.genericExpression0_6, part0.genericExpression0_7, part0.genericExpression0_8]

noncomputable def genericExpressions1 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression1_0, part0.genericExpression1_1, part0.genericExpression1_2, part0.genericExpression1_3, part0.genericExpression1_4, part0.genericExpression1_5, part0.genericExpression1_6, part0.genericExpression1_7, part0.genericExpression1_8]

noncomputable def genericExpressions2 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression2_0, part0.genericExpression2_1, part0.genericExpression2_2, part0.genericExpression2_3, part0.genericExpression2_4, part0.genericExpression2_5, part0.genericExpression2_6, part0.genericExpression2_7, part0.genericExpression2_8]

noncomputable def genericExpressions3 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression3_0, part0.genericExpression3_1, part0.genericExpression3_2, part0.genericExpression3_3, part0.genericExpression3_4, part0.genericExpression3_5, part0.genericExpression3_6, part0.genericExpression3_7, part0.genericExpression3_8]

noncomputable def genericExpressions4 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression4_0, part0.genericExpression4_1, part0.genericExpression4_2, part0.genericExpression4_3, part0.genericExpression4_4, part0.genericExpression4_5, part0.genericExpression4_6, part0.genericExpression4_7, part0.genericExpression4_8]

noncomputable def genericExpressions5 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression5_0, part0.genericExpression5_1, part0.genericExpression5_2, part0.genericExpression5_3, part0.genericExpression5_4, part0.genericExpression5_5, part0.genericExpression5_6, part0.genericExpression5_7, part0.genericExpression5_8]

noncomputable def genericExpressions6 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression6_0, part0.genericExpression6_1, part0.genericExpression6_2, part0.genericExpression6_3, part0.genericExpression6_4, part0.genericExpression6_5, part0.genericExpression6_6, part0.genericExpression6_7, part0.genericExpression6_8]

noncomputable def genericExpressions7 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression7_0, part0.genericExpression7_1, part0.genericExpression7_2, part0.genericExpression7_3, part0.genericExpression7_4, part0.genericExpression7_5, part0.genericExpression7_6, part0.genericExpression7_7, part0.genericExpression7_8]

noncomputable def genericExpressions8 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part1.genericExpression8_0, part1.genericExpression8_1, part1.genericExpression8_2, part1.genericExpression8_3, part1.genericExpression8_4, part1.genericExpression8_5, part1.genericExpression8_6, part1.genericExpression8_7, part1.genericExpression8_8]

noncomputable def genericExpressions9 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part1.genericExpression9_0, part1.genericExpression9_1, part1.genericExpression9_2, part1.genericExpression9_3, part1.genericExpression9_4, part1.genericExpression9_5, part1.genericExpression9_6, part1.genericExpression9_7, part1.genericExpression9_8]

noncomputable def genericExpressions10 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part1.genericExpression10_0, part1.genericExpression10_1, part1.genericExpression10_2, part1.genericExpression10_3, part1.genericExpression10_4, part1.genericExpression10_5, part1.genericExpression10_6, part1.genericExpression10_7, part1.genericExpression10_8]

noncomputable def genericExpressions11 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part1.genericExpression11_0, part1.genericExpression11_1, part1.genericExpression11_2, part1.genericExpression11_3, part1.genericExpression11_4, part1.genericExpression11_5, part1.genericExpression11_6, part1.genericExpression11_7, part1.genericExpression11_8]

noncomputable def genericExpressions12 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part1.genericExpression12_0, part1.genericExpression12_1, part1.genericExpression12_2, part1.genericExpression12_3, part1.genericExpression12_4, part1.genericExpression12_5, part1.genericExpression12_6, part1.genericExpression12_7, part1.genericExpression12_8]

noncomputable def genericExpressions13 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part1.genericExpression13_0, part1.genericExpression13_1, part1.genericExpression13_2, part1.genericExpression13_3, part1.genericExpression13_4, part1.genericExpression13_5, part1.genericExpression13_6, part1.genericExpression13_7, part1.genericExpression13_8]

noncomputable def genericExpressions14 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part1.genericExpression14_0, part1.genericExpression14_1, part1.genericExpression14_2, part1.genericExpression14_3, part1.genericExpression14_4, part1.genericExpression14_5, part1.genericExpression14_6, part1.genericExpression14_7, part1.genericExpression14_8]

noncomputable def genericExpressions15 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part1.genericExpression15_0, part1.genericExpression15_1, part1.genericExpression15_2, part1.genericExpression15_3, part1.genericExpression15_4, part1.genericExpression15_5, part1.genericExpression15_6, part1.genericExpression15_7, part1.genericExpression15_8]

noncomputable def genericExpressions16 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part2.genericExpression16_0, part2.genericExpression16_1, part2.genericExpression16_2, part2.genericExpression16_3, part2.genericExpression16_4, part2.genericExpression16_5, part2.genericExpression16_6, part2.genericExpression16_7, part2.genericExpression16_8]

noncomputable def genericExpressions17 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part2.genericExpression17_0, part2.genericExpression17_1, part2.genericExpression17_2, part2.genericExpression17_3, part2.genericExpression17_4, part2.genericExpression17_5, part2.genericExpression17_6, part2.genericExpression17_7, part2.genericExpression17_8]

noncomputable def genericExpressions18 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part2.genericExpression18_0, part2.genericExpression18_1, part2.genericExpression18_2, part2.genericExpression18_3, part2.genericExpression18_4, part2.genericExpression18_5, part2.genericExpression18_6, part2.genericExpression18_7, part2.genericExpression18_8]

noncomputable def genericExpressions : List (Vector (_root_.Expression Source.BaseField) 9) :=
  [genericExpressions0, genericExpressions1, genericExpressions2, genericExpressions3, genericExpressions4, genericExpressions5, genericExpressions6, genericExpressions7, genericExpressions8, genericExpressions9, genericExpressions10, genericExpressions11, genericExpressions12, genericExpressions13, genericExpressions14, genericExpressions15, genericExpressions16, genericExpressions17, genericExpressions18]

end native

end Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached
