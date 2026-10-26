import Airbender.Import.GKRProtocol.HelperImport
import Airbender.Proofs.GKRProtocol.MemoryNative.AddSubCached
import Airbender.Proofs.GKRProtocol.LookupNative.AddSubCached

namespace Airbender.Compiler.HelperNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_helpers native from "artifacts/compiler/add-sub-cached.json"
  source "artifacts/compiler/add-sub-cached-source.json"
  selectors "{\"format_version\":1,\"addresses\":[{\"BaseLayerMemory\":18},{\"BaseLayerMemory\":19},{\"BaseLayerMemory\":20},{\"BaseLayerMemory\":21},{\"BaseLayerMemory\":17},{\"BaseLayerMemory\":4},{\"BaseLayerMemory\":9},{\"BaseLayerMemory\":14},{\"BaseLayerWitness\":0},{\"BaseLayerWitness\":1},{\"BaseLayerWitness\":2},{\"BaseLayerWitness\":3},{\"BaseLayerWitness\":4},{\"BaseLayerWitness\":5},{\"BaseLayerWitness\":6},{\"BaseLayerWitness\":7},{\"BaseLayerWitness\":8},{\"BaseLayerWitness\":9},{\"BaseLayerWitness\":10},{\"BaseLayerMemory\":22},{\"BaseLayerMemory\":23},{\"BaseLayerMemory\":24},{\"BaseLayerMemory\":25},{\"BaseLayerMemory\":0},{\"BaseLayerMemory\":1},{\"BaseLayerMemory\":2},{\"BaseLayerMemory\":3},{\"BaseLayerMemory\":5},{\"BaseLayerMemory\":6},{\"BaseLayerMemory\":7},{\"BaseLayerMemory\":8},{\"BaseLayerMemory\":12},{\"BaseLayerMemory\":13},{\"BaseLayerMemory\":15},{\"BaseLayerMemory\":16},{\"BaseLayerMemory\":10},{\"BaseLayerMemory\":11},{\"BaseLayerWitness\":11},{\"BaseLayerWitness\":12},{\"BaseLayerWitness\":13},{\"BaseLayerWitness\":14},{\"BaseLayerWitness\":15},{\"BaseLayerWitness\":16},{\"BaseLayerWitness\":17},{\"BaseLayerWitness\":18},{\"BaseLayerWitness\":19},{\"BaseLayerWitness\":20},{\"BaseLayerWitness\":21},{\"InnerLayer\":{\"layer\":1,\"offset\":0}},{\"InnerLayer\":{\"layer\":1,\"offset\":11}},{\"Cached\":{\"layer\":0,\"offset\":13}},{\"InnerLayer\":{\"layer\":1,\"offset\":20}},{\"InnerLayer\":{\"layer\":2,\"offset\":0}},{\"VirtualSetup\":\"InitsAndTeardownsLow\"},{\"VirtualSetup\":\"InitsAndTeardownsHigh\"}],\"operands\":[{\"native_leaf\":6,\"locator\":[9,0],\"expansion\":[],\"source_index\":0,\"witness\":[]},{\"native_leaf\":8,\"locator\":[10,0],\"expansion\":[],\"source_index\":1,\"witness\":[]},{\"native_leaf\":9,\"locator\":[10,1],\"expansion\":[8],\"source_index\":2,\"witness\":[]},{\"native_leaf\":10,\"locator\":[11,0],\"expansion\":[9],\"source_index\":3,\"witness\":[]},{\"native_leaf\":11,\"locator\":[11,1],\"expansion\":[10],\"source_index\":4,\"witness\":[]},{\"native_leaf\":12,\"locator\":[12,0],\"expansion\":[11],\"source_index\":5,\"witness\":[]},{\"native_leaf\":13,\"locator\":[12,1],\"expansion\":[12],\"source_index\":6,\"witness\":[]},{\"native_leaf\":17,\"locator\":[50,0],\"expansion\":[18,13],\"source_index\":7,\"witness\":[]}],\"setup_leaf\":7,\"group\":{\"native_leaves\":[12,13,17,6,7,10,11,8,9],\"source_labels\":[5,6,7,0,8,3,4,1,2]}}"
  memory_model Airbender.Compiler.MemoryNative.AddSubCached.native
  lookup_model Airbender.Compiler.LookupNative.AddSubCached.native
  typing Airbender.Compiler.ConsumerNative.AddSubCached.native.typing

end Airbender.Compiler.HelperNative.AddSubCached
