import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedFoundation
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps0
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps1
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps2
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps3
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps4
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps5
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps6
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps7
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps8
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedSteps9
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedBase0
import Airbender.Proofs.GKRProtocol.FunctionalNative.BigintCachedBase1
import Airbender.Import.GKRProtocol.FunctionalFinalize

namespace Airbender.Compiler.FunctionalNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

finalize_checked_functional_graph native selectors "{\"steps\":294,\"affine_steps\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,null,null,null,null,null,204,205,216,217,233,234,null,237,240,247,248,254,255,null,265,267,271,272,null,285,286],\"base\":[{\"affine\":40,\"gate\":0},{\"affine\":41,\"gate\":1},{\"affine\":42,\"gate\":2},{\"affine\":43,\"gate\":3},{\"affine\":44,\"gate\":4},{\"affine\":45,\"gate\":5},{\"affine\":46,\"gate\":6},{\"affine\":47,\"gate\":7},{\"affine\":48,\"gate\":8},{\"affine\":49,\"gate\":9},{\"affine\":50,\"gate\":10},{\"affine\":51,\"gate\":11},{\"affine\":52,\"gate\":12},{\"affine\":53,\"gate\":13},{\"affine\":54,\"gate\":14},{\"affine\":55,\"gate\":15},{\"affine\":56,\"gate\":16},{\"affine\":57,\"gate\":17},{\"affine\":58,\"gate\":18},{\"affine\":59,\"gate\":19},{\"affine\":60,\"gate\":20},{\"affine\":61,\"gate\":21},{\"affine\":62,\"gate\":22},{\"affine\":63,\"gate\":23},{\"affine\":64,\"gate\":24},{\"affine\":65,\"gate\":25},{\"affine\":66,\"gate\":26},{\"affine\":67,\"gate\":27},{\"affine\":68,\"gate\":28},{\"affine\":69,\"gate\":29},{\"affine\":70,\"gate\":30},{\"affine\":71,\"gate\":31},{\"affine\":72,\"gate\":32},{\"affine\":73,\"gate\":33},{\"affine\":74,\"gate\":34},{\"affine\":75,\"gate\":35},{\"affine\":76,\"gate\":36},{\"affine\":77,\"gate\":37},{\"affine\":78,\"gate\":38},{\"affine\":79,\"gate\":39},{\"affine\":80,\"gate\":40},{\"affine\":143,\"gate\":41},{\"affine\":144,\"gate\":59},{\"affine\":145,\"gate\":60},{\"affine\":146,\"gate\":61},{\"affine\":147,\"gate\":176},{\"affine\":154,\"gate\":179},{\"affine\":161,\"gate\":180},{\"affine\":166,\"gate\":181}],\"lookup_steps\":[122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,237,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,265,267,268,269,270,271,272,273,274,275,276,277,278,279,282,283,284,285,286,287,288,291,292,293],\"product_steps\":[102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,182,183,184,185,186,187,188,189,190,191,204,205,216,217,233,234,235,236,237,238,239,240,247,248,254,255,264,265,266,267,271,272,280,281,285,286,289,290]}"
  lookup Airbender.Compiler.LookupNative.BigintCached.native
  product Airbender.Compiler.ProductNative.BigintCached.native
  base Airbender.Compiler.FullArithmeticNative.BigintCached.native

end Airbender.Compiler.FunctionalNative.BigintCached
