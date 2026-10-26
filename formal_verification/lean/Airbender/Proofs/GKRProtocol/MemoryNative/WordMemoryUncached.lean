import Airbender.Import.GKRProtocol.MemoryImport
import Airbender.Proofs.GKRProtocol.ProductNative.WordMemoryUncached

namespace Airbender.Compiler.MemoryNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_memory native from "artifacts/compiler/word-memory-uncached.json"
  source "artifacts/compiler/word-memory-uncached-source.json"
  selectors "{\"format_version\":1,\"addresses\":[{\"BaseLayerMemory\":21},{\"BaseLayerMemory\":22},{\"BaseLayerMemory\":23},{\"BaseLayerMemory\":24},{\"BaseLayerMemory\":20},{\"BaseLayerMemory\":4},{\"BaseLayerWitness\":0},{\"BaseLayerWitness\":1},{\"BaseLayerWitness\":2},{\"BaseLayerWitness\":3},{\"BaseLayerMemory\":9},{\"BaseLayerMemory\":25},{\"BaseLayerMemory\":26},{\"BaseLayerMemory\":27},{\"BaseLayerMemory\":28},{\"BaseLayerMemory\":0},{\"BaseLayerMemory\":1},{\"BaseLayerMemory\":2},{\"BaseLayerMemory\":3},{\"BaseLayerMemory\":10},{\"BaseLayerMemory\":11},{\"BaseLayerMemory\":5},{\"BaseLayerMemory\":6},{\"BaseLayerMemory\":7},{\"BaseLayerMemory\":8},{\"BaseLayerMemory\":16},{\"BaseLayerMemory\":17},{\"BaseLayerMemory\":12},{\"BaseLayerMemory\":13},{\"BaseLayerMemory\":14},{\"BaseLayerMemory\":15},{\"BaseLayerMemory\":18},{\"BaseLayerMemory\":19},{\"InnerLayer\":{\"layer\":1,\"offset\":5}},{\"InnerLayer\":{\"layer\":1,\"offset\":6}},{\"BaseLayerWitness\":4},{\"InnerLayer\":{\"layer\":1,\"offset\":7}},{\"InnerLayer\":{\"layer\":1,\"offset\":8}},{\"InnerLayer\":{\"layer\":1,\"offset\":9}},{\"InnerLayer\":{\"layer\":2,\"offset\":0}},{\"InnerLayer\":{\"layer\":1,\"offset\":10}},{\"InnerLayer\":{\"layer\":2,\"offset\":1}},{\"InnerLayer\":{\"layer\":1,\"offset\":11}},{\"InnerLayer\":{\"layer\":2,\"offset\":2}},{\"InnerLayer\":{\"layer\":1,\"offset\":12}},{\"InnerLayer\":{\"layer\":2,\"offset\":3}},{\"BaseLayerWitness\":5},{\"BaseLayerWitness\":6},{\"BaseLayerWitness\":7},{\"BaseLayerWitness\":8},{\"BaseLayerWitness\":9},{\"BaseLayerWitness\":10},{\"InnerLayer\":{\"layer\":1,\"offset\":0}},{\"InnerLayer\":{\"layer\":1,\"offset\":15}},{\"InnerLayer\":{\"layer\":2,\"offset\":4}},{\"InnerLayer\":{\"layer\":2,\"offset\":9}},{\"VirtualSetup\":\"InitsAndTeardownsLow\"},{\"VirtualSetup\":\"InitsAndTeardownsHigh\"}],\"leaves\":[{\"native_leaf\":0,\"locator\":[1,0],\"expansion\":[]},{\"native_leaf\":1,\"locator\":[1,1],\"expansion\":[]},{\"native_leaf\":2,\"locator\":[2,0],\"expansion\":[]},{\"native_leaf\":3,\"locator\":[2,1],\"expansion\":[]},{\"native_leaf\":4,\"locator\":[3,0],\"expansion\":[]},{\"native_leaf\":5,\"locator\":[3,1],\"expansion\":[]},{\"native_leaf\":6,\"locator\":[4,0],\"expansion\":[]},{\"native_leaf\":7,\"locator\":[4,1],\"expansion\":[]}],\"groups\":{\"memoryRead\":{\"native_leaves\":[0,1,4,5],\"source_labels\":[0,1,2,3],\"witnesses\":[[],[],[],[]],\"mask\":{\"address\":{\"InnerLayer\":{\"layer\":2,\"offset\":4}},\"witness\":[[[[2013265920,[]]],0],[[[2013265920,[]]],6]]}},\"memoryWrite\":{\"native_leaves\":[2,3,6,7],\"source_labels\":[0,1,2,3],\"witnesses\":[[],[],[],[]],\"mask\":{\"address\":{\"InnerLayer\":{\"layer\":2,\"offset\":4}},\"witness\":[[[[2013265920,[]]],0],[[[2013265920,[]]],6]]}}},\"counts\":{\"registry\":8,\"occurrences\":8,\"nonempty_witnesses\":0}}"
  word_bits 2
  native_model Airbender.Compiler.ProductNative.WordMemoryUncached.native
  typing Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing

end Airbender.Compiler.MemoryNative.WordMemoryUncached
