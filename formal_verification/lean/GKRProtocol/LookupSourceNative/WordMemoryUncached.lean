import GKRProtocol.LookupSourceImport
import GKRProtocol.Native.WordMemoryUncached
import GKRProtocol.LookupNative.WordMemoryUncached

namespace Airbender.Compiler.LookupSourceNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_lookups native from "artifacts/compiler/word-memory-uncached.json"
  certificate "artifacts/compiler/lookup/word-memory-uncached.json"
  selectors "{\"format_version\":1,\"operands\":[{\"native_leaf\":0,\"locator\":[13,0],\"expansion\":[],\"group\":\"Lookup16Bits\",\"source_row\":2,\"fields\":[[]],\"kind\":\"query\",\"source_index\":1},{\"native_leaf\":1,\"locator\":[13,1],\"expansion\":[],\"group\":\"Lookup16Bits\",\"source_row\":null,\"fields\":[],\"kind\":\"setup\"},{\"native_leaf\":2,\"locator\":[15,0],\"expansion\":[],\"group\":\"LookupTimestamps\",\"source_row\":null,\"fields\":[],\"kind\":\"timestamp\",\"source_index\":0},{\"native_leaf\":3,\"locator\":[15,1],\"expansion\":[],\"group\":\"LookupTimestamps\",\"source_row\":null,\"fields\":[],\"kind\":\"setup\"},{\"native_leaf\":4,\"locator\":[16,0],\"expansion\":[],\"group\":\"LookupTimestamps\",\"source_row\":null,\"fields\":[],\"kind\":\"timestamp\",\"source_index\":1},{\"native_leaf\":5,\"locator\":[16,1],\"expansion\":[],\"group\":\"LookupTimestamps\",\"source_row\":null,\"fields\":[],\"kind\":\"timestamp\",\"source_index\":2},{\"native_leaf\":6,\"locator\":[17,0],\"expansion\":[],\"group\":\"LookupTimestamps\",\"source_row\":null,\"fields\":[],\"kind\":\"timestamp\",\"source_index\":3},{\"native_leaf\":7,\"locator\":[17,1],\"expansion\":[],\"group\":\"LookupTimestamps\",\"source_row\":null,\"fields\":[],\"kind\":\"timestamp\",\"source_index\":4},{\"native_leaf\":8,\"locator\":[18,0],\"expansion\":[],\"group\":\"LookupTimestamps\",\"source_row\":null,\"fields\":[],\"kind\":\"timestamp\",\"source_index\":5},{\"native_leaf\":9,\"locator\":[18,1],\"expansion\":[],\"group\":\"LookupTimestamps\",\"source_row\":null,\"fields\":[],\"kind\":\"timestamp\",\"source_index\":6},{\"native_leaf\":10,\"locator\":[20,0],\"expansion\":[],\"group\":\"GenericLookup\",\"source_row\":4,\"fields\":[[],[],[],[],[],[],[],[],[],[]],\"kind\":\"decoder\"},{\"native_leaf\":11,\"locator\":[20,1],\"expansion\":[],\"group\":\"GenericLookup\",\"source_row\":null,\"fields\":[],\"kind\":\"setup\"},{\"native_leaf\":12,\"locator\":[41,0],\"expansion\":[3],\"group\":\"Lookup16Bits\",\"source_row\":3,\"fields\":[[]],\"kind\":\"query\",\"source_index\":2},{\"native_leaf\":13,\"locator\":[43,0],\"expansion\":[4],\"group\":\"LookupTimestamps\",\"source_row\":null,\"fields\":[],\"kind\":\"timestamp\",\"source_index\":7},{\"native_leaf\":14,\"locator\":[53,0],\"expansion\":[8],\"group\":\"Lookup16Bits\",\"source_row\":1,\"fields\":[[]],\"kind\":\"query\",\"source_index\":0},{\"native_leaf\":15,\"locator\":[57,0],\"expansion\":[],\"group\":\"GenericLookup\",\"source_row\":0,\"fields\":[[],[],[],[],[],[],[],[],[]],\"kind\":\"query\",\"source_index\":0}],\"groups\":{\"GenericLookup\":{\"native_leaves\":[10,11,15],\"source_labels\":[1,2,0]},\"Lookup16Bits\":{\"native_leaves\":[0,1,12,14],\"source_labels\":[1,3,2,0]},\"LookupTimestamps\":{\"native_leaves\":[8,9,13,2,3,6,7,4,5],\"source_labels\":[5,6,7,0,8,3,4,1,2]}},\"counts\":{\"definitions\":21,\"registry\":16,\"source_fields\":22,\"nonempty_witnesses\":0}}"
  reference Airbender.Compiler.LookupNative.WordMemoryUncached.native
  typing Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing
  phase 3 start 0 stop 16

end Airbender.Compiler.LookupSourceNative.WordMemoryUncached
