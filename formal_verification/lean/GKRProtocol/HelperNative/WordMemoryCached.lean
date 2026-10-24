import GKRProtocol.HelperImport
import GKRProtocol.MemoryNative.WordMemoryCached
import GKRProtocol.LookupNative.WordMemoryCached

namespace Airbender.Compiler.HelperNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_helpers native from "artifacts/compiler/word-memory-cached.json"
  source "artifacts/compiler/word-memory-cached-source.json"
  selectors "{\"format_version\":1,\"addresses\":[{\"BaseLayerMemory\":21},{\"BaseLayerMemory\":22},{\"BaseLayerMemory\":23},{\"BaseLayerMemory\":24},{\"BaseLayerMemory\":20},{\"BaseLayerMemory\":4},{\"BaseLayerWitness\":0},{\"BaseLayerWitness\":1},{\"BaseLayerWitness\":2},{\"BaseLayerWitness\":3},{\"BaseLayerMemory\":9},{\"BaseLayerMemory\":25},{\"BaseLayerMemory\":26},{\"BaseLayerMemory\":27},{\"BaseLayerMemory\":28},{\"BaseLayerMemory\":0},{\"BaseLayerMemory\":1},{\"BaseLayerMemory\":2},{\"BaseLayerMemory\":3},{\"BaseLayerMemory\":10},{\"BaseLayerMemory\":11},{\"BaseLayerMemory\":5},{\"BaseLayerMemory\":6},{\"BaseLayerMemory\":7},{\"BaseLayerMemory\":8},{\"BaseLayerMemory\":16},{\"BaseLayerMemory\":17},{\"BaseLayerMemory\":12},{\"BaseLayerMemory\":13},{\"BaseLayerMemory\":14},{\"BaseLayerMemory\":15},{\"BaseLayerMemory\":18},{\"BaseLayerMemory\":19},{\"InnerLayer\":{\"layer\":1,\"offset\":5}},{\"InnerLayer\":{\"layer\":1,\"offset\":6}},{\"BaseLayerWitness\":4},{\"InnerLayer\":{\"layer\":1,\"offset\":7}},{\"InnerLayer\":{\"layer\":1,\"offset\":8}},{\"InnerLayer\":{\"layer\":1,\"offset\":9}},{\"InnerLayer\":{\"layer\":2,\"offset\":0}},{\"InnerLayer\":{\"layer\":1,\"offset\":10}},{\"InnerLayer\":{\"layer\":2,\"offset\":1}},{\"InnerLayer\":{\"layer\":1,\"offset\":11}},{\"InnerLayer\":{\"layer\":2,\"offset\":2}},{\"InnerLayer\":{\"layer\":1,\"offset\":12}},{\"InnerLayer\":{\"layer\":2,\"offset\":3}},{\"BaseLayerWitness\":5},{\"BaseLayerWitness\":6},{\"BaseLayerWitness\":7},{\"BaseLayerWitness\":8},{\"BaseLayerWitness\":9},{\"BaseLayerWitness\":10},{\"InnerLayer\":{\"layer\":1,\"offset\":0}},{\"InnerLayer\":{\"layer\":1,\"offset\":15}},{\"Cached\":{\"layer\":0,\"offset\":13}},{\"InnerLayer\":{\"layer\":1,\"offset\":24}},{\"InnerLayer\":{\"layer\":2,\"offset\":4}},{\"InnerLayer\":{\"layer\":2,\"offset\":9}},{\"VirtualSetup\":\"InitsAndTeardownsLow\"},{\"VirtualSetup\":\"InitsAndTeardownsHigh\"}],\"operands\":[{\"native_leaf\":2,\"locator\":[15,0],\"expansion\":[],\"source_index\":0,\"witness\":[]},{\"native_leaf\":4,\"locator\":[16,0],\"expansion\":[],\"source_index\":1,\"witness\":[]},{\"native_leaf\":5,\"locator\":[16,1],\"expansion\":[8],\"source_index\":2,\"witness\":[]},{\"native_leaf\":6,\"locator\":[17,0],\"expansion\":[9],\"source_index\":3,\"witness\":[]},{\"native_leaf\":7,\"locator\":[17,1],\"expansion\":[10],\"source_index\":4,\"witness\":[]},{\"native_leaf\":8,\"locator\":[18,0],\"expansion\":[11],\"source_index\":5,\"witness\":[]},{\"native_leaf\":9,\"locator\":[18,1],\"expansion\":[12],\"source_index\":6,\"witness\":[]},{\"native_leaf\":13,\"locator\":[43,0],\"expansion\":[21,13],\"source_index\":7,\"witness\":[]}],\"setup_leaf\":3,\"group\":{\"native_leaves\":[8,9,13,2,3,6,7,4,5],\"source_labels\":[5,6,7,0,8,3,4,1,2]}}"
  memory_model Airbender.Compiler.MemoryNative.WordMemoryCached.native
  lookup_model Airbender.Compiler.LookupNative.WordMemoryCached.native
  typing Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing

end Airbender.Compiler.HelperNative.WordMemoryCached
