import Airbender.Proofs.Keccak.SplitPermutationDefinitions

namespace Airbender.Keccak.Split.Call.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

-- The finite proof below checks every index against the unchanged reference.
private def slotCache : Vector (Vector (Fin 31) 7) 361 := #v[
#v[0, 5, 10, 15, 20, 25, 30],
#v[1, 6, 11, 16, 21, 26, 30],
#v[2, 7, 12, 17, 22, 27, 30],
#v[3, 8, 13, 18, 23, 28, 30],
#v[4, 9, 14, 19, 24, 29, 30],
#v[0, 5, 10, 15, 20, 29, 26],
#v[1, 6, 11, 16, 21, 25, 27],
#v[2, 7, 12, 17, 22, 26, 28],
#v[3, 8, 13, 18, 23, 27, 29],
#v[4, 9, 14, 19, 24, 28, 25],
#v[0, 6, 12, 18, 24, 30, 30],
#v[10, 16, 22, 3, 9, 30, 30],
#v[20, 1, 7, 13, 19, 30, 30],
#v[5, 11, 17, 23, 4, 30, 30],
#v[15, 21, 2, 8, 14, 30, 30],
#v[0, 3, 1, 4, 2, 25, 30],
#v[6, 9, 7, 5, 8, 26, 30],
#v[12, 10, 13, 11, 14, 27, 30],
#v[18, 16, 19, 17, 15, 28, 30],
#v[24, 22, 20, 23, 21, 29, 30],
#v[0, 3, 1, 4, 2, 29, 26],
#v[6, 9, 7, 5, 8, 25, 27],
#v[12, 10, 13, 11, 14, 26, 28],
#v[18, 16, 19, 17, 15, 27, 29],
#v[24, 22, 20, 23, 21, 28, 25],
#v[0, 9, 13, 17, 21, 30, 30],
#v[1, 5, 14, 18, 22, 30, 30],
#v[2, 6, 10, 19, 23, 30, 30],
#v[3, 7, 11, 15, 24, 30, 30],
#v[4, 8, 12, 16, 20, 30, 30],
#v[0, 18, 6, 24, 12, 25, 30],
#v[9, 22, 10, 3, 16, 26, 30],
#v[13, 1, 19, 7, 20, 27, 30],
#v[17, 5, 23, 11, 4, 28, 30],
#v[21, 14, 2, 15, 8, 29, 30],
#v[0, 18, 6, 24, 12, 29, 26],
#v[9, 22, 10, 3, 16, 25, 27],
#v[13, 1, 19, 7, 20, 26, 28],
#v[17, 5, 23, 11, 4, 27, 29],
#v[21, 14, 2, 15, 8, 28, 25],
#v[0, 22, 19, 11, 8, 30, 30],
#v[6, 3, 20, 17, 14, 30, 30],
#v[12, 9, 1, 23, 15, 30, 30],
#v[18, 10, 7, 4, 21, 30, 30],
#v[24, 16, 13, 5, 2, 30, 30],
#v[0, 17, 9, 21, 13, 25, 30],
#v[22, 14, 1, 18, 5, 26, 30],
#v[19, 6, 23, 10, 2, 27, 30],
#v[11, 3, 15, 7, 24, 28, 30],
#v[8, 20, 12, 4, 16, 29, 30],
#v[0, 17, 9, 21, 13, 29, 26],
#v[22, 14, 1, 18, 5, 25, 27],
#v[19, 6, 23, 10, 2, 26, 28],
#v[11, 3, 15, 7, 24, 27, 29],
#v[8, 20, 12, 4, 16, 28, 25],
#v[0, 14, 23, 7, 16, 30, 30],
#v[9, 18, 2, 11, 20, 30, 30],
#v[13, 22, 6, 15, 4, 30, 30],
#v[17, 1, 10, 24, 8, 30, 30],
#v[21, 5, 19, 3, 12, 30, 30],
#v[0, 11, 22, 8, 19, 25, 30],
#v[14, 20, 6, 17, 3, 26, 30],
#v[23, 9, 15, 1, 12, 27, 30],
#v[7, 18, 4, 10, 21, 28, 30],
#v[16, 2, 13, 24, 5, 29, 30],
#v[0, 11, 22, 8, 19, 29, 26],
#v[14, 20, 6, 17, 3, 25, 27],
#v[23, 9, 15, 1, 12, 26, 28],
#v[7, 18, 4, 10, 21, 27, 29],
#v[16, 2, 13, 24, 5, 28, 25],
#v[0, 20, 15, 10, 5, 30, 30],
#v[22, 17, 12, 7, 2, 30, 30],
#v[19, 14, 9, 4, 24, 30, 30],
#v[11, 6, 1, 21, 16, 30, 30],
#v[8, 3, 23, 18, 13, 30, 30],
#v[0, 7, 14, 16, 23, 25, 30],
#v[20, 2, 9, 11, 18, 26, 30],
#v[15, 22, 4, 6, 13, 27, 30],
#v[10, 17, 24, 1, 8, 28, 30],
#v[5, 12, 19, 21, 3, 29, 30],
#v[0, 7, 14, 16, 23, 29, 26],
#v[20, 2, 9, 11, 18, 25, 27],
#v[15, 22, 4, 6, 13, 26, 28],
#v[10, 17, 24, 1, 8, 27, 29],
#v[5, 12, 19, 21, 3, 28, 25],
#v[0, 2, 4, 1, 3, 30, 30],
#v[14, 11, 13, 10, 12, 30, 30],
#v[23, 20, 22, 24, 21, 30, 30],
#v[7, 9, 6, 8, 5, 30, 30],
#v[16, 18, 15, 17, 19, 30, 30],
#v[0, 10, 20, 5, 15, 25, 30],
#v[2, 12, 22, 7, 17, 26, 30],
#v[4, 14, 24, 9, 19, 27, 30],
#v[1, 11, 21, 6, 16, 28, 30],
#v[3, 13, 23, 8, 18, 29, 30],
#v[0, 10, 20, 5, 15, 29, 26],
#v[2, 12, 22, 7, 17, 25, 27],
#v[4, 14, 24, 9, 19, 26, 28],
#v[1, 11, 21, 6, 16, 27, 29],
#v[3, 13, 23, 8, 18, 28, 25],
#v[0, 12, 24, 6, 18, 30, 30],
#v[20, 7, 19, 1, 13, 30, 30],
#v[15, 2, 14, 21, 8, 30, 30],
#v[10, 22, 9, 16, 3, 30, 30],
#v[5, 17, 4, 11, 23, 30, 30],
#v[0, 1, 2, 3, 4, 25, 30],
#v[12, 13, 14, 10, 11, 26, 30],
#v[24, 20, 21, 22, 23, 27, 30],
#v[6, 7, 8, 9, 5, 28, 30],
#v[18, 19, 15, 16, 17, 29, 30],
#v[0, 1, 2, 3, 4, 29, 26],
#v[12, 13, 14, 10, 11, 25, 27],
#v[24, 20, 21, 22, 23, 26, 28],
#v[6, 7, 8, 9, 5, 27, 29],
#v[18, 19, 15, 16, 17, 28, 25],
#v[0, 13, 21, 9, 17, 30, 30],
#v[2, 10, 23, 6, 19, 30, 30],
#v[4, 12, 20, 8, 16, 30, 30],
#v[1, 14, 22, 5, 18, 30, 30],
#v[3, 11, 24, 7, 15, 30, 30],
#v[0, 6, 12, 18, 24, 25, 30],
#v[13, 19, 20, 1, 7, 26, 30],
#v[21, 2, 8, 14, 15, 27, 30],
#v[9, 10, 16, 22, 3, 28, 30],
#v[17, 23, 4, 5, 11, 29, 30],
#v[0, 6, 12, 18, 24, 29, 26],
#v[13, 19, 20, 1, 7, 25, 27],
#v[21, 2, 8, 14, 15, 26, 28],
#v[9, 10, 16, 22, 3, 27, 29],
#v[17, 23, 4, 5, 11, 28, 25],
#v[0, 19, 8, 22, 11, 30, 30],
#v[12, 1, 15, 9, 23, 30, 30],
#v[24, 13, 2, 16, 5, 30, 30],
#v[6, 20, 14, 3, 17, 30, 30],
#v[18, 7, 21, 10, 4, 30, 30],
#v[0, 9, 13, 17, 21, 25, 30],
#v[19, 23, 2, 6, 10, 26, 30],
#v[8, 12, 16, 20, 4, 27, 30],
#v[22, 1, 5, 14, 18, 28, 30],
#v[11, 15, 24, 3, 7, 29, 30],
#v[0, 9, 13, 17, 21, 29, 26],
#v[19, 23, 2, 6, 10, 25, 27],
#v[8, 12, 16, 20, 4, 26, 28],
#v[22, 1, 5, 14, 18, 27, 29],
#v[11, 15, 24, 3, 7, 28, 25],
#v[0, 23, 16, 14, 7, 30, 30],
#v[13, 6, 4, 22, 15, 30, 30],
#v[21, 19, 12, 5, 3, 30, 30],
#v[9, 2, 20, 18, 11, 30, 30],
#v[17, 10, 8, 1, 24, 30, 30],
#v[0, 22, 19, 11, 8, 25, 30],
#v[23, 15, 12, 9, 1, 26, 30],
#v[16, 13, 5, 2, 24, 27, 30],
#v[14, 6, 3, 20, 17, 28, 30],
#v[7, 4, 21, 18, 10, 29, 30],
#v[0, 22, 19, 11, 8, 29, 26],
#v[23, 15, 12, 9, 1, 25, 27],
#v[16, 13, 5, 2, 24, 26, 28],
#v[14, 6, 3, 20, 17, 27, 29],
#v[7, 4, 21, 18, 10, 28, 25],
#v[0, 15, 5, 20, 10, 30, 30],
#v[19, 9, 24, 14, 4, 30, 30],
#v[8, 23, 13, 3, 18, 30, 30],
#v[22, 12, 2, 17, 7, 30, 30],
#v[11, 1, 16, 6, 21, 30, 30],
#v[0, 14, 23, 7, 16, 25, 30],
#v[15, 4, 13, 22, 6, 26, 30],
#v[5, 19, 3, 12, 21, 27, 30],
#v[20, 9, 18, 2, 11, 28, 30],
#v[10, 24, 8, 17, 1, 29, 30],
#v[0, 14, 23, 7, 16, 29, 26],
#v[15, 4, 13, 22, 6, 25, 27],
#v[5, 19, 3, 12, 21, 26, 28],
#v[20, 9, 18, 2, 11, 27, 29],
#v[10, 24, 8, 17, 1, 28, 25],
#v[0, 4, 3, 2, 1, 30, 30],
#v[23, 22, 21, 20, 24, 30, 30],
#v[16, 15, 19, 18, 17, 30, 30],
#v[14, 13, 12, 11, 10, 30, 30],
#v[7, 6, 5, 9, 8, 30, 30],
#v[0, 20, 15, 10, 5, 25, 30],
#v[4, 24, 19, 14, 9, 26, 30],
#v[3, 23, 18, 13, 8, 27, 30],
#v[2, 22, 17, 12, 7, 28, 30],
#v[1, 21, 16, 11, 6, 29, 30],
#v[0, 20, 15, 10, 5, 29, 26],
#v[4, 24, 19, 14, 9, 25, 27],
#v[3, 23, 18, 13, 8, 26, 28],
#v[2, 22, 17, 12, 7, 27, 29],
#v[1, 21, 16, 11, 6, 28, 25],
#v[0, 24, 18, 12, 6, 30, 30],
#v[15, 14, 8, 2, 21, 30, 30],
#v[5, 4, 23, 17, 11, 30, 30],
#v[20, 19, 13, 7, 1, 30, 30],
#v[10, 9, 3, 22, 16, 30, 30],
#v[0, 2, 4, 1, 3, 25, 30],
#v[24, 21, 23, 20, 22, 26, 30],
#v[18, 15, 17, 19, 16, 27, 30],
#v[12, 14, 11, 13, 10, 28, 30],
#v[6, 8, 5, 7, 9, 29, 30],
#v[0, 2, 4, 1, 3, 29, 26],
#v[24, 21, 23, 20, 22, 25, 27],
#v[18, 15, 17, 19, 16, 26, 28],
#v[12, 14, 11, 13, 10, 27, 29],
#v[6, 8, 5, 7, 9, 28, 25],
#v[0, 21, 17, 13, 9, 30, 30],
#v[4, 20, 16, 12, 8, 30, 30],
#v[3, 24, 15, 11, 7, 30, 30],
#v[2, 23, 19, 10, 6, 30, 30],
#v[1, 22, 18, 14, 5, 30, 30],
#v[0, 12, 24, 6, 18, 25, 30],
#v[21, 8, 15, 2, 14, 26, 30],
#v[17, 4, 11, 23, 5, 27, 30],
#v[13, 20, 7, 19, 1, 28, 30],
#v[9, 16, 3, 10, 22, 29, 30],
#v[0, 12, 24, 6, 18, 29, 26],
#v[21, 8, 15, 2, 14, 25, 27],
#v[17, 4, 11, 23, 5, 26, 28],
#v[13, 20, 7, 19, 1, 27, 29],
#v[9, 16, 3, 10, 22, 28, 25],
#v[0, 8, 11, 19, 22, 30, 30],
#v[24, 2, 5, 13, 16, 30, 30],
#v[18, 21, 4, 7, 10, 30, 30],
#v[12, 15, 23, 1, 9, 30, 30],
#v[6, 14, 17, 20, 3, 30, 30],
#v[0, 13, 21, 9, 17, 25, 30],
#v[8, 16, 4, 12, 20, 26, 30],
#v[11, 24, 7, 15, 3, 27, 30],
#v[19, 2, 10, 23, 6, 28, 30],
#v[22, 5, 18, 1, 14, 29, 30],
#v[0, 13, 21, 9, 17, 29, 26],
#v[8, 16, 4, 12, 20, 25, 27],
#v[11, 24, 7, 15, 3, 26, 28],
#v[19, 2, 10, 23, 6, 27, 29],
#v[22, 5, 18, 1, 14, 28, 25],
#v[0, 16, 7, 23, 14, 30, 30],
#v[21, 12, 3, 19, 5, 30, 30],
#v[17, 8, 24, 10, 1, 30, 30],
#v[13, 4, 15, 6, 22, 30, 30],
#v[9, 20, 11, 2, 18, 30, 30],
#v[0, 19, 8, 22, 11, 25, 30],
#v[16, 5, 24, 13, 2, 26, 30],
#v[7, 21, 10, 4, 18, 27, 30],
#v[23, 12, 1, 15, 9, 28, 30],
#v[14, 3, 17, 6, 20, 29, 30],
#v[0, 19, 8, 22, 11, 29, 26],
#v[16, 5, 24, 13, 2, 25, 27],
#v[7, 21, 10, 4, 18, 26, 28],
#v[23, 12, 1, 15, 9, 27, 29],
#v[14, 3, 17, 6, 20, 28, 25],
#v[0, 5, 10, 15, 20, 30, 30],
#v[8, 13, 18, 23, 3, 30, 30],
#v[11, 16, 21, 1, 6, 30, 30],
#v[19, 24, 4, 9, 14, 30, 30],
#v[22, 2, 7, 12, 17, 30, 30],
#v[0, 23, 16, 14, 7, 25, 30],
#v[5, 3, 21, 19, 12, 26, 30],
#v[10, 8, 1, 24, 17, 27, 30],
#v[15, 13, 6, 4, 22, 28, 30],
#v[20, 18, 11, 9, 2, 29, 30],
#v[0, 23, 16, 14, 7, 29, 26],
#v[5, 3, 21, 19, 12, 25, 27],
#v[10, 8, 1, 24, 17, 26, 28],
#v[15, 13, 6, 4, 22, 27, 29],
#v[20, 18, 11, 9, 2, 28, 25],
#v[0, 3, 1, 4, 2, 30, 30],
#v[16, 19, 17, 15, 18, 30, 30],
#v[7, 5, 8, 6, 9, 30, 30],
#v[23, 21, 24, 22, 20, 30, 30],
#v[14, 12, 10, 13, 11, 30, 30],
#v[0, 15, 5, 20, 10, 25, 30],
#v[3, 18, 8, 23, 13, 26, 30],
#v[1, 16, 6, 21, 11, 27, 30],
#v[4, 19, 9, 24, 14, 28, 30],
#v[2, 17, 7, 22, 12, 29, 30],
#v[0, 15, 5, 20, 10, 29, 26],
#v[3, 18, 8, 23, 13, 25, 27],
#v[1, 16, 6, 21, 11, 26, 28],
#v[4, 19, 9, 24, 14, 27, 29],
#v[2, 17, 7, 22, 12, 28, 25],
#v[0, 18, 6, 24, 12, 30, 30],
#v[5, 23, 11, 4, 17, 30, 30],
#v[10, 3, 16, 9, 22, 30, 30],
#v[15, 8, 21, 14, 2, 30, 30],
#v[20, 13, 1, 19, 7, 30, 30],
#v[0, 4, 3, 2, 1, 25, 30],
#v[18, 17, 16, 15, 19, 26, 30],
#v[6, 5, 9, 8, 7, 27, 30],
#v[24, 23, 22, 21, 20, 28, 30],
#v[12, 11, 10, 14, 13, 29, 30],
#v[0, 4, 3, 2, 1, 29, 26],
#v[18, 17, 16, 15, 19, 25, 27],
#v[6, 5, 9, 8, 7, 26, 28],
#v[24, 23, 22, 21, 20, 27, 29],
#v[12, 11, 10, 14, 13, 28, 25],
#v[0, 17, 9, 21, 13, 30, 30],
#v[3, 15, 7, 24, 11, 30, 30],
#v[1, 18, 5, 22, 14, 30, 30],
#v[4, 16, 8, 20, 12, 30, 30],
#v[2, 19, 6, 23, 10, 30, 30],
#v[0, 24, 18, 12, 6, 25, 30],
#v[17, 11, 5, 4, 23, 26, 30],
#v[9, 3, 22, 16, 10, 27, 30],
#v[21, 15, 14, 8, 2, 28, 30],
#v[13, 7, 1, 20, 19, 29, 30],
#v[0, 24, 18, 12, 6, 29, 26],
#v[17, 11, 5, 4, 23, 25, 27],
#v[9, 3, 22, 16, 10, 26, 28],
#v[21, 15, 14, 8, 2, 27, 29],
#v[13, 7, 1, 20, 19, 28, 25],
#v[0, 11, 22, 8, 19, 30, 30],
#v[18, 4, 10, 21, 7, 30, 30],
#v[6, 17, 3, 14, 20, 30, 30],
#v[24, 5, 16, 2, 13, 30, 30],
#v[12, 23, 9, 15, 1, 30, 30],
#v[0, 21, 17, 13, 9, 25, 30],
#v[11, 7, 3, 24, 15, 26, 30],
#v[22, 18, 14, 5, 1, 27, 30],
#v[8, 4, 20, 16, 12, 28, 30],
#v[19, 10, 6, 2, 23, 29, 30],
#v[0, 21, 17, 13, 9, 29, 26],
#v[11, 7, 3, 24, 15, 25, 27],
#v[22, 18, 14, 5, 1, 26, 28],
#v[8, 4, 20, 16, 12, 27, 29],
#v[19, 10, 6, 2, 23, 28, 25],
#v[0, 7, 14, 16, 23, 30, 30],
#v[17, 24, 1, 8, 10, 30, 30],
#v[9, 11, 18, 20, 2, 30, 30],
#v[21, 3, 5, 12, 19, 30, 30],
#v[13, 15, 22, 4, 6, 30, 30],
#v[0, 8, 11, 19, 22, 25, 30],
#v[7, 10, 18, 21, 4, 26, 30],
#v[14, 17, 20, 3, 6, 27, 30],
#v[16, 24, 2, 5, 13, 28, 30],
#v[23, 1, 9, 12, 15, 29, 30],
#v[0, 8, 11, 19, 22, 29, 26],
#v[7, 10, 18, 21, 4, 25, 27],
#v[14, 17, 20, 3, 6, 26, 28],
#v[16, 24, 2, 5, 13, 27, 29],
#v[23, 1, 9, 12, 15, 28, 25],
#v[0, 10, 20, 5, 15, 30, 30],
#v[11, 21, 6, 16, 1, 30, 30],
#v[22, 7, 17, 2, 12, 30, 30],
#v[8, 18, 3, 13, 23, 30, 30],
#v[19, 4, 14, 24, 9, 30, 30],
#v[0, 16, 7, 23, 14, 25, 30],
#v[10, 1, 17, 8, 24, 26, 30],
#v[20, 11, 2, 18, 9, 27, 30],
#v[5, 21, 12, 3, 19, 28, 30],
#v[15, 6, 22, 13, 4, 29, 30],
#v[0, 16, 7, 23, 14, 29, 26],
#v[10, 1, 17, 8, 24, 25, 27],
#v[20, 11, 2, 18, 9, 26, 28],
#v[5, 21, 12, 3, 19, 27, 29],
#v[15, 6, 22, 13, 4, 28, 25],
#v[0, 1, 2, 3, 4, 30, 30],
#v[7, 8, 9, 5, 6, 30, 30],
#v[14, 10, 11, 12, 13, 30, 30],
#v[16, 17, 18, 19, 15, 30, 30],
#v[23, 24, 20, 21, 22, 30, 30],
#v[0, 5, 10, 15, 20, 25, 30]]

-- Each closed kernel computation covers at most one fifteen-call round.
-- Keep the original whole-cache contract; assemble all 361 cases below.
private def cacheEntryCorrect (index : Fin 361) : Prop :=
  slots index = slotCache[index]

private def cachePart (base width : Nat) (fits : base + width ≤ 361)
    (i : Fin width) : Fin 361 := ⟨base + i.val, by omega⟩

private theorem cacheCorrect0 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 0 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect1 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 15 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect2 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 30 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect3 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 45 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect4 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 60 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect5 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 75 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect6 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 90 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect7 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 105 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect8 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 120 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect9 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 135 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect10 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 150 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect11 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 165 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect12 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 180 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect13 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 195 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect14 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 210 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect15 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 225 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect16 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 240 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect17 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 255 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect18 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 270 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect19 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 285 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect20 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 300 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect21 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 315 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect22 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 330 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect23 : ∀ i : Fin 15,
    cacheEntryCorrect (cachePart 345 15 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem cacheCorrect24 : ∀ i : Fin 1,
    cacheEntryCorrect (cachePart 360 1 (by decide) i) := by
  simp only [cacheEntryCorrect, cachePart]
  decide +kernel

private theorem slot_cache_correct : ∀ index : Fin 361, slots index = slotCache[index] := by
  intro index
  have bound := index.isLt
  change cacheEntryCorrect index
  by_cases h0 : index.val < 15
  · simpa only [cachePart, Nat.zero_add] using cacheCorrect0 ⟨index.val, h0⟩
  by_cases h1 : index.val < 30
  · simpa only [cachePart, show 15 + (index.val - 15) = index.val by omega] using
      cacheCorrect1 ⟨index.val - 15, by omega⟩
  by_cases h2 : index.val < 45
  · simpa only [cachePart, show 30 + (index.val - 30) = index.val by omega] using
      cacheCorrect2 ⟨index.val - 30, by omega⟩
  by_cases h3 : index.val < 60
  · simpa only [cachePart, show 45 + (index.val - 45) = index.val by omega] using
      cacheCorrect3 ⟨index.val - 45, by omega⟩
  by_cases h4 : index.val < 75
  · simpa only [cachePart, show 60 + (index.val - 60) = index.val by omega] using
      cacheCorrect4 ⟨index.val - 60, by omega⟩
  by_cases h5 : index.val < 90
  · simpa only [cachePart, show 75 + (index.val - 75) = index.val by omega] using
      cacheCorrect5 ⟨index.val - 75, by omega⟩
  by_cases h6 : index.val < 105
  · simpa only [cachePart, show 90 + (index.val - 90) = index.val by omega] using
      cacheCorrect6 ⟨index.val - 90, by omega⟩
  by_cases h7 : index.val < 120
  · simpa only [cachePart, show 105 + (index.val - 105) = index.val by omega] using
      cacheCorrect7 ⟨index.val - 105, by omega⟩
  by_cases h8 : index.val < 135
  · simpa only [cachePart, show 120 + (index.val - 120) = index.val by omega] using
      cacheCorrect8 ⟨index.val - 120, by omega⟩
  by_cases h9 : index.val < 150
  · simpa only [cachePart, show 135 + (index.val - 135) = index.val by omega] using
      cacheCorrect9 ⟨index.val - 135, by omega⟩
  by_cases h10 : index.val < 165
  · simpa only [cachePart, show 150 + (index.val - 150) = index.val by omega] using
      cacheCorrect10 ⟨index.val - 150, by omega⟩
  by_cases h11 : index.val < 180
  · simpa only [cachePart, show 165 + (index.val - 165) = index.val by omega] using
      cacheCorrect11 ⟨index.val - 165, by omega⟩
  by_cases h12 : index.val < 195
  · simpa only [cachePart, show 180 + (index.val - 180) = index.val by omega] using
      cacheCorrect12 ⟨index.val - 180, by omega⟩
  by_cases h13 : index.val < 210
  · simpa only [cachePart, show 195 + (index.val - 195) = index.val by omega] using
      cacheCorrect13 ⟨index.val - 195, by omega⟩
  by_cases h14 : index.val < 225
  · simpa only [cachePart, show 210 + (index.val - 210) = index.val by omega] using
      cacheCorrect14 ⟨index.val - 210, by omega⟩
  by_cases h15 : index.val < 240
  · simpa only [cachePart, show 225 + (index.val - 225) = index.val by omega] using
      cacheCorrect15 ⟨index.val - 225, by omega⟩
  by_cases h16 : index.val < 255
  · simpa only [cachePart, show 240 + (index.val - 240) = index.val by omega] using
      cacheCorrect16 ⟨index.val - 240, by omega⟩
  by_cases h17 : index.val < 270
  · simpa only [cachePart, show 255 + (index.val - 255) = index.val by omega] using
      cacheCorrect17 ⟨index.val - 255, by omega⟩
  by_cases h18 : index.val < 285
  · simpa only [cachePart, show 270 + (index.val - 270) = index.val by omega] using
      cacheCorrect18 ⟨index.val - 270, by omega⟩
  by_cases h19 : index.val < 300
  · simpa only [cachePart, show 285 + (index.val - 285) = index.val by omega] using
      cacheCorrect19 ⟨index.val - 285, by omega⟩
  by_cases h20 : index.val < 315
  · simpa only [cachePart, show 300 + (index.val - 300) = index.val by omega] using
      cacheCorrect20 ⟨index.val - 300, by omega⟩
  by_cases h21 : index.val < 330
  · simpa only [cachePart, show 315 + (index.val - 315) = index.val by omega] using
      cacheCorrect21 ⟨index.val - 315, by omega⟩
  by_cases h22 : index.val < 345
  · simpa only [cachePart, show 330 + (index.val - 330) = index.val by omega] using
      cacheCorrect22 ⟨index.val - 330, by omega⟩
  by_cases h23 : index.val < 360
  · simpa only [cachePart, show 345 + (index.val - 345) = index.val by omega] using
      cacheCorrect23 ⟨index.val - 345, by omega⟩
  · simpa only [cachePart, show 360 + (index.val - 360) = index.val by omega] using
      cacheCorrect24 ⟨index.val - 360, by omega⟩

/-- Reuse the kernel-checked physical slot cache in native layout bindings. -/
theorem slots_normalized (index : Fin 361) : slots index = slotCache[index] :=
  slot_cache_correct index

private def normalizedStep (index : Fin 361) (state : LaneState) : LaneState :=
  let positions := slotCache[index]
  let input := Vector.ofFn fun lane : Fin 7 => state positions[lane]
  fun physical =>
    let slot := positions.toList.idxOf physical
    if active : slot < slotCount (kindAt index.val) then
      (result index input)[slot]'(lt_of_lt_of_le active (slot_count_bound _))
    else state physical

/-- Cache only the fixed indices; retain the original symbolic lane operation. -/
theorem micro_normalized (index : Fin 361) (state : LaneState) :
    microStep index state = normalizedStep index state := by
  unfold microStep normalizedStep
  simp only [slot_cache_correct]

end Airbender.Keccak.Split.Call.Proofs
