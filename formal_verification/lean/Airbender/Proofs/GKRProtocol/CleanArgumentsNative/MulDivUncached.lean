import Airbender.Import.GKRProtocol.CleanLookupArgumentsImport
import Airbender.Import.GKRProtocol.CleanHelperArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.MulDivUncached

namespace Airbender.Compiler.CleanArgumentsNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_lookup_arguments native from "artifacts/compiler/mul-div-uncached.json"
  certificate "artifacts/compiler/lookup/mul-div-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivUncached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivUncached.native

import_clean_helper_arguments native from "artifacts/compiler/mul-div-uncached.json"
  helper_indices "{\"format_version\":1,\"addresses\":[{\"BaseLayerMemory\":18},{\"BaseLayerMemory\":19},{\"BaseLayerMemory\":20},{\"BaseLayerMemory\":21},{\"BaseLayerMemory\":17},{\"BaseLayerMemory\":4},{\"BaseLayerMemory\":9},{\"BaseLayerMemory\":14},{\"BaseLayerWitness\":0},{\"BaseLayerWitness\":1},{\"BaseLayerWitness\":2},{\"BaseLayerWitness\":3},{\"BaseLayerWitness\":4},{\"BaseLayerWitness\":5},{\"BaseLayerMemory\":22},{\"BaseLayerMemory\":23},{\"BaseLayerMemory\":24},{\"BaseLayerMemory\":25},{\"BaseLayerMemory\":0},{\"BaseLayerMemory\":1},{\"BaseLayerMemory\":2},{\"BaseLayerMemory\":3},{\"BaseLayerMemory\":5},{\"BaseLayerMemory\":6},{\"BaseLayerMemory\":7},{\"BaseLayerMemory\":8},{\"BaseLayerMemory\":12},{\"BaseLayerMemory\":13},{\"BaseLayerMemory\":15},{\"BaseLayerMemory\":16},{\"BaseLayerMemory\":10},{\"BaseLayerMemory\":11},{\"BaseLayerWitness\":6},{\"BaseLayerWitness\":7},{\"BaseLayerWitness\":8},{\"BaseLayerWitness\":9},{\"BaseLayerWitness\":10},{\"BaseLayerWitness\":11},{\"BaseLayerWitness\":12},{\"BaseLayerWitness\":13},{\"BaseLayerWitness\":14},{\"BaseLayerWitness\":15},{\"BaseLayerWitness\":16},{\"BaseLayerWitness\":17},{\"InnerLayer\":{\"layer\":1,\"offset\":5}},{\"InnerLayer\":{\"layer\":1,\"offset\":6}},{\"InnerLayer\":{\"layer\":1,\"offset\":7}},{\"InnerLayer\":{\"layer\":1,\"offset\":8}},{\"InnerLayer\":{\"layer\":1,\"offset\":9}},{\"InnerLayer\":{\"layer\":1,\"offset\":10}},{\"InnerLayer\":{\"layer\":1,\"offset\":11}},{\"InnerLayer\":{\"layer\":1,\"offset\":12}},{\"InnerLayer\":{\"layer\":1,\"offset\":13}},{\"InnerLayer\":{\"layer\":1,\"offset\":14}},{\"InnerLayer\":{\"layer\":1,\"offset\":15}},{\"InnerLayer\":{\"layer\":1,\"offset\":16}},{\"InnerLayer\":{\"layer\":1,\"offset\":17}},{\"InnerLayer\":{\"layer\":1,\"offset\":18}},{\"InnerLayer\":{\"layer\":1,\"offset\":19}},{\"InnerLayer\":{\"layer\":1,\"offset\":20}},{\"InnerLayer\":{\"layer\":1,\"offset\":21}},{\"InnerLayer\":{\"layer\":1,\"offset\":22}},{\"InnerLayer\":{\"layer\":1,\"offset\":23}},{\"InnerLayer\":{\"layer\":1,\"offset\":24}},{\"InnerLayer\":{\"layer\":1,\"offset\":25}},{\"BaseLayerWitness\":18},{\"BaseLayerWitness\":19},{\"BaseLayerWitness\":20},{\"BaseLayerWitness\":21},{\"BaseLayerWitness\":22},{\"BaseLayerWitness\":23},{\"InnerLayer\":{\"layer\":1,\"offset\":0}},{\"InnerLayer\":{\"layer\":1,\"offset\":34}},{\"InnerLayer\":{\"layer\":2,\"offset\":0}},{\"VirtualSetup\":\"InitsAndTeardownsLow\"},{\"VirtualSetup\":\"InitsAndTeardownsHigh\"}],\"operands\":[{\"native_leaf\":8,\"locator\":[31,0],\"expansion\":[],\"source_index\":0,\"witness\":[]},{\"native_leaf\":10,\"locator\":[32,0],\"expansion\":[],\"source_index\":1,\"witness\":[]},{\"native_leaf\":11,\"locator\":[32,1],\"expansion\":[],\"source_index\":2,\"witness\":[]},{\"native_leaf\":12,\"locator\":[33,0],\"expansion\":[],\"source_index\":3,\"witness\":[]},{\"native_leaf\":13,\"locator\":[33,1],\"expansion\":[],\"source_index\":4,\"witness\":[]},{\"native_leaf\":14,\"locator\":[34,0],\"expansion\":[],\"source_index\":5,\"witness\":[]},{\"native_leaf\":15,\"locator\":[34,1],\"expansion\":[],\"source_index\":6,\"witness\":[]},{\"native_leaf\":25,\"locator\":[59,0],\"expansion\":[11],\"source_index\":7,\"witness\":[]}],\"setup_leaf\":9,\"group\":{\"native_leaves\":[14,15,25,8,9,12,13,10,11],\"source_labels\":[5,6,7,0,8,3,4,1,2]}}"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  helper_model Airbender.Compiler.HelperNative.MulDivUncached.native
  memory_model Airbender.Compiler.MemoryNative.MulDivUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivUncached.native

end Airbender.Compiler.CleanArgumentsNative.MulDivUncached
