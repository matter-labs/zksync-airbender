import GKRProtocol.ChunkSpans

namespace Airbender.Compiler
set_option warningAsError true

theorem sixteen_region_shape0 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = ([]) ++ (a0 ++ (a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc, List.nil_append]

theorem sixteen_region_shape1 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0) ++ (a1 ++ (a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape2 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1) ++ (a2 ++ (a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape3 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2) ++ (a3 ++ (a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape4 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3) ++ (a4 ++ (a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape5 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4) ++ (a5 ++ (a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5) ++ (a6 ++ (a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape7 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6) ++ (a7 ++ (a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape8 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7) ++ (a8 ++ (a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8) ++ (a9 ++ (a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9) ++ (a10 ++ (a11 ++ a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape11 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10) ++ (a11 ++ (a12 ++ a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape12 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11) ++ (a12 ++ (a13 ++ a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12) ++ (a13 ++ (a14 ++ a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape14 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13) ++ (a14 ++ (a15)) := by
  simp only [List.append_assoc]

theorem sixteen_region_shape15 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : List Setup.Block) :
    a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14 ++ a15 = (a0 ++ a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7 ++ a8 ++ a9 ++ a10 ++ a11 ++ a12 ++ a13 ++ a14) ++ (a15 ++ ([])) := by
  simp only [List.append_assoc, List.append_nil]

end Airbender.Compiler
