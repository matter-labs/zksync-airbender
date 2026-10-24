import GKRProtocol.MemoryImport
import GKRProtocol.ProductNative.JumpBranchCached

namespace Airbender.Compiler.MemoryNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_memory native from "artifacts/compiler/jump-branch-cached.json"
  source "artifacts/compiler/jump-branch-cached-source.json"
  selectors "{\"format_version\":1,\"addresses\":[{\"BaseLayerMemory\":18},{\"BaseLayerMemory\":19},{\"BaseLayerMemory\":20},{\"BaseLayerMemory\":21},{\"BaseLayerMemory\":17},{\"BaseLayerMemory\":4},{\"BaseLayerMemory\":9},{\"BaseLayerMemory\":14},{\"BaseLayerWitness\":0},{\"BaseLayerWitness\":1},{\"BaseLayerWitness\":2},{\"BaseLayerWitness\":3},{\"BaseLayerWitness\":4},{\"BaseLayerWitness\":5},{\"BaseLayerWitness\":6},{\"BaseLayerWitness\":7},{\"BaseLayerMemory\":22},{\"BaseLayerMemory\":23},{\"BaseLayerMemory\":24},{\"BaseLayerMemory\":25},{\"BaseLayerMemory\":0},{\"BaseLayerMemory\":1},{\"BaseLayerMemory\":2},{\"BaseLayerMemory\":3},{\"BaseLayerMemory\":5},{\"BaseLayerMemory\":6},{\"BaseLayerMemory\":7},{\"BaseLayerMemory\":8},{\"BaseLayerMemory\":12},{\"BaseLayerMemory\":13},{\"BaseLayerMemory\":15},{\"BaseLayerMemory\":16},{\"BaseLayerMemory\":10},{\"BaseLayerMemory\":11},{\"BaseLayerWitness\":8},{\"BaseLayerWitness\":9},{\"BaseLayerWitness\":10},{\"BaseLayerWitness\":11},{\"BaseLayerWitness\":12},{\"BaseLayerWitness\":13},{\"BaseLayerWitness\":14},{\"BaseLayerWitness\":15},{\"BaseLayerWitness\":16},{\"BaseLayerWitness\":17},{\"BaseLayerWitness\":18},{\"BaseLayerWitness\":19},{\"BaseLayerWitness\":20},{\"BaseLayerWitness\":21},{\"BaseLayerWitness\":22},{\"BaseLayerWitness\":23},{\"BaseLayerWitness\":24},{\"BaseLayerWitness\":25},{\"BaseLayerWitness\":26},{\"BaseLayerWitness\":27},{\"BaseLayerWitness\":28},{\"InnerLayer\":{\"layer\":1,\"offset\":0}},{\"InnerLayer\":{\"layer\":1,\"offset\":9}},{\"Cached\":{\"layer\":0,\"offset\":13}},{\"InnerLayer\":{\"layer\":1,\"offset\":18}},{\"InnerLayer\":{\"layer\":2,\"offset\":0}},{\"VirtualSetup\":\"InitsAndTeardownsLow\"},{\"VirtualSetup\":\"InitsAndTeardownsHigh\"}],\"leaves\":[{\"native_leaf\":0,\"locator\":[1,0],\"expansion\":[0]},{\"native_leaf\":1,\"locator\":[1,1],\"expansion\":[1]},{\"native_leaf\":2,\"locator\":[2,0],\"expansion\":[2]},{\"native_leaf\":3,\"locator\":[2,1],\"expansion\":[3]},{\"native_leaf\":4,\"locator\":[3,0],\"expansion\":[4]},{\"native_leaf\":5,\"locator\":[3,1],\"expansion\":[5]},{\"native_leaf\":6,\"locator\":[4,0],\"expansion\":[6]},{\"native_leaf\":7,\"locator\":[4,1],\"expansion\":[7]}],\"groups\":{\"memoryRead\":{\"native_leaves\":[0,1,4,5],\"source_labels\":[0,1,2,3],\"witnesses\":[[],[],[],[]],\"mask\":{\"address\":{\"InnerLayer\":{\"layer\":2,\"offset\":0}},\"witness\":[[[[2013265920,[]]],0],[[[2013265920,[]]],3]]}},\"memoryWrite\":{\"native_leaves\":[2,3,6,7],\"source_labels\":[0,1,2,3],\"witnesses\":[[],[],[],[]],\"mask\":{\"address\":{\"InnerLayer\":{\"layer\":2,\"offset\":0}},\"witness\":[[[[2013265920,[]]],0],[[[2013265920,[]]],3]]}}},\"counts\":{\"registry\":8,\"occurrences\":8,\"nonempty_witnesses\":0}}"
  word_bits 2
  native_model Airbender.Compiler.ProductNative.JumpBranchCached.native
  typing Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing

end Airbender.Compiler.MemoryNative.JumpBranchCached
