import AtlasCut

namespace AtlasCutRow3320D6
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

private def cols : List W := [0x60c183060c183000000001fffff,0x3870e1c3870e1c000007ffe00000,0xc183060c183060fffff800000000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0x204081020408100003f8001fc000,0x204081020408101fc000fe00000,0x4081020408102fe0007f0000000]
private def s6_0 : State := [0x204081020408101fc000fe00000,0x4081020408102fe0007f0000000,0x60c183060c183000000001fffff,0x204081020408100003f8001fc000,0x3870e1c3870e1c000007ffe00000,0xc183060c183060fffff800000000,0xd9b366cd9b366c00000000003fff]
private theorem tail0 : optimized 6 0 s6_0 = false := by decide +kernel
private def s6_1 : State := [0x204081020408101fc000fe00000,0x4081020408102fe0007f0000000,0x60c183060c183000000001fffff,0x3870e1c3870e1c000007ffe00000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0xe1c3870e1c3870fffff8001fc000]
private theorem tail1 : optimized 6 0 s6_1 = false := by decide +kernel
private def s6_2 : State := [0x204081020408101fc000fe00000,0x4081020408102fe0007f0000000,0x204081020408100003f8001fc000,0x3870e1c3870e1c000007ffe00000,0x489122448912240000000000007f,0x972e5cb972e5cb000000001fffff,0xc183060c183060fffff800000000]
private theorem tail2 : optimized 6 0 s6_2 = false := by decide +kernel
private def s6_3 : State := [0x204081020408101fc000fe00000,0x4081020408102fe0007f0000000,0x204081020408100003f8001fc000,0x3870e1c3870e1c000007ffe00000,0x4e9d3a74e9d3a7000000001fffff,0x9122448912244800000000003f80,0xc183060c183060fffff800000000]
private theorem tail3 : optimized 6 0 s6_3 = false := by decide +kernel
private def s6_4 : State := [0x204081020408101fc000fe00000,0x4081020408102fe0007f0000000,0x264c993264c9930003f8001fffff,0x3870e1c3870e1c000007ffe00000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0xc183060c183060fffff800000000]
private theorem tail4 : optimized 6 0 s6_4 = false := by decide +kernel
private def s6_5 : State := [0x204081020408101fc000fe00000,0x60c183060c183000000001fffff,0x204081020408100003f8001fc000,0x3870e1c3870e1c000007ffe00000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0xc58b162c58b162fffffff0000000]
private theorem tail5 : optimized 6 0 s6_5 = false := by decide +kernel
private def s6_6 : State := [0x204081020408101fc000fe00000,0x60c183060c183000000001fffff,0x204081020408100003f8001fc000,0x3c78f1e3c78f1efe0007ffe00000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0xc183060c183060fffff800000000]
private theorem tail6 : optimized 6 0 s6_6 = false := by decide +kernel
private def s6_7 : State := [0x4081020408102fe0007f0000000,0x60c183060c183000000001fffff,0x204081020408100003f8001fc000,0x3870e1c3870e1c000007ffe00000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0xc3870e1c3870e1fffff80fe00000]
private theorem tail7 : optimized 6 0 s6_7 = false := by decide +kernel
private def s6_8 : State := [0x4081020408102fe0007f0000000,0x60c183060c183000000001fffff,0x204081020408100003f8001fc000,0x3a74e9d3a74e9d01fc07ffe00000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0xc183060c183060fffff800000000]
private theorem tail8 : optimized 6 0 s6_8 = false := by decide +kernel
private def s6_9 : State := [0x60c183060c183000000001fffff,0x60c183060c183fffc07ffe00000,0x204081020408100003f8001fc000,0x3870e1c3870e1c000007ffe00000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0xc183060c183060fffff800000000]
private theorem tail9 : optimized 6 0 s6_9 = false := by decide +kernel
private def layer6 : Layer := #[s6_0,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s6_7,s6_8,s6_9]
private def s7_0 : State := [0x204081020408101fc000fe00000,0x4081020408102fe0007f0000000,0x60c183060c183000000001fffff,0x204081020408100003f8001fc000,0x3870e1c3870e1c000007ffe00000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0xc183060c183060fffff800000000]
private def layer7 : Layer := #[s7_0]
private def cert : Table := #[#[],#[],#[],#[],#[],#[],layer6,layer7]
private theorem anchor6 : AtlasCut.Anchors 6 layer6 := by
  intro s mem nd
  simp only [layer6, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact AtlasCut.leaf tail0 nd
  · exact AtlasCut.leaf tail1 nd
  · exact AtlasCut.leaf tail2 nd
  · exact AtlasCut.leaf tail3 nd
  · exact AtlasCut.leaf tail4 nd
  · exact AtlasCut.leaf tail5 nd
  · exact AtlasCut.leaf tail6 nd
  · exact AtlasCut.leaf tail7 nd
  · exact AtlasCut.leaf tail8 nd
  · exact AtlasCut.leaf tail9 nd
private theorem flags7 : layer7.all (stateOK layer6 7) = true := by decide +kernel
private theorem anchor7 : AtlasCut.Anchors 7 layer7 := AtlasCut.step anchor6 flags7
theorem result : AtlasLower.lower 3320 8 :=
  AtlasCut.sound (samp := sample 3320) (k := 7) (xs := cols) cert
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) anchor7

end AtlasCutRow3320D6
