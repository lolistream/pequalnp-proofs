import AtlasCut

namespace AtlasCutRow1148D6
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

private def cols : List W := [0xc71c71c71c71c7c0000000000fff,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0x1041041041041000000fc0000fc0,0x410410410410410003f00003f000,0x8208208208208200fc0000fc0000,0x41041041041043f00003f000000]
private def s6_0 : State := [0x41041041041043f00003f000000,0x1041041041041000000fc0000fc0,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0xc30c30c30c30c300fff000fff000,0xc71c71c71c71c7c0000000000fff]
private theorem tail0 : optimized 6 0 s6_0 = false := by decide +kernel
private def s6_1 : State := [0x41041041041043f00003f000000,0x1041041041041000000fc0000fc0,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x410410410410410003f00003f000,0x8208208208208200fc0000fc0000,0xefbefbefbefbefc0000000000fff]
private theorem tail1 : optimized 6 0 s6_1 = false := by decide +kernel
private def s6_2 : State := [0x41041041041043f00003f000000,0x1041041041041000000fc0000fc0,0x186186186186180000003ffff000,0x28a28a28a28a28c000000000003f,0x410410410410410003f00003f000,0xa28a28a28a28a23fffffc0fc0000,0xc71c71c71c71c7c0000000000fff]
private theorem tail2 : optimized 6 0 s6_2 = false := by decide +kernel
private def s6_3 : State := [0x41041041041043f00003f000000,0x1041041041041000000fc0000fc0,0x186186186186180000003ffff000,0x28a28a28a28a28c000000000003f,0x618618618618613fffffc003f000,0x8208208208208200fc0000fc0000,0xc71c71c71c71c7c0000000000fff]
private theorem tail3 : optimized 6 0 s6_3 = false := by decide +kernel
private def s6_4 : State := [0x41041041041043f00003f000000,0x1041041041041000000fc0000fc0,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0x410410410410410003f00003f000,0x9a69a69a69a69a00fc003ffff000,0xc71c71c71c71c7c0000000000fff]
private theorem tail4 : optimized 6 0 s6_4 = false := by decide +kernel
private def s6_5 : State := [0x41041041041043f00003f000000,0x1041041041041000000fc0000fc0,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0x596596596596590003f03ffff000,0x8208208208208200fc0000fc0000,0xc71c71c71c71c7c0000000000fff]
private theorem tail5 : optimized 6 0 s6_5 = false := by decide +kernel
private def s6_6 : State := [0x41041041041043f00003f000000,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0x410410410410410003f00003f000,0x8208208208208200fc0000fc0000,0xd75d75d75d75d7c0000fc0000fff]
private theorem tail6 : optimized 6 0 s6_6 = false := by decide +kernel
private def s6_7 : State := [0x41041041041043f00003f000000,0x186186186186180000003ffff000,0x28a28a28a28a28c000000000003f,0x30c30c30c30c303fffffc0000fc0,0x410410410410410003f00003f000,0x8208208208208200fc0000fc0000,0xc71c71c71c71c7c0000000000fff]
private theorem tail7 : optimized 6 0 s6_7 = false := by decide +kernel
private def s6_8 : State := [0x1041041041041000000fc0000fc0,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0x410410410410410003f00003f000,0x861861861861863ffc003ffc0000,0xc71c71c71c71c7c0000000000fff]
private theorem tail8 : optimized 6 0 s6_8 = false := by decide +kernel
private def s6_9 : State := [0x1041041041041000000fc0000fc0,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0x451451451451453f03f03f03f000,0x8208208208208200fc0000fc0000,0xc71c71c71c71c7c0000000000fff]
private theorem tail9 : optimized 6 0 s6_9 = false := by decide +kernel
private def s6_10 : State := [0x1041041041041000000fc0000fc0,0x186186186186180000003ffff000,0x249249249249243fffffff000000,0x28a28a28a28a28c000000000003f,0x410410410410410003f00003f000,0x8208208208208200fc0000fc0000,0xc71c71c71c71c7c0000000000fff]
private theorem tail10 : optimized 6 0 s6_10 = false := by decide +kernel
private def s6_11 : State := [0x1041041041041000000fc0000fc0,0x1c71c71c71c71c3f00003ffff000,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0x410410410410410003f00003f000,0x8208208208208200fc0000fc0000,0xc71c71c71c71c7c0000000000fff]
private theorem tail11 : optimized 6 0 s6_11 = false := by decide +kernel
private def layer6 : Layer := #[s6_0,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s6_7,s6_8,s6_9,s6_10,s6_11]
private def s7_0 : State := [0x41041041041043f00003f000000,0x1041041041041000000fc0000fc0,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0x410410410410410003f00003f000,0x8208208208208200fc0000fc0000,0xc71c71c71c71c7c0000000000fff]
private def layer7 : Layer := #[s7_0]
private def cert : Table := #[#[],#[],#[],#[],#[],#[],layer6,layer7]
private theorem anchor6 : AtlasCut.Anchors 6 layer6 := by
  intro s mem nd
  simp only [layer6, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact AtlasCut.leaf tail10 nd
  · exact AtlasCut.leaf tail11 nd
private theorem flags7 : layer7.all (stateOK layer6 7) = true := by decide +kernel
private theorem anchor7 : AtlasCut.Anchors 7 layer7 := AtlasCut.step anchor6 flags7
theorem result : AtlasLower.lower 1148 8 :=
  AtlasCut.sound (samp := sample 1148) (k := 7) (xs := cols) cert
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) anchor7

end AtlasCutRow1148D6
