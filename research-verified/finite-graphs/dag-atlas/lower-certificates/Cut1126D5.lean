import AtlasCut

namespace AtlasCutRow1126D5
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

private def cols : List W := [0x8c6318c6318c63fc000000007fff,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0xa5294a5294a529000007c0000000,0x84210842108420000f8000f8000,0x801f0001f003e0,0x3e0003e007c00]
private def s5_0 : State := [0x3e0003e007c00,0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0xa5294a5294a529000007c0000000,0xdef7bdef7bdef7fc000000007fff]
private theorem tail0 : optimized 5 0 s5_0 = false := by decide +kernel
private def s5_1 : State := [0x3e0003e007c00,0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xe739ce739ce73903ffffc0000000]
private theorem tail1 : optimized 5 0 s5_1 = false := by decide +kernel
private def s5_2 : State := [0x3e0003e007c00,0x318c6318c6318c0000003fff8000,0x4a5294a5294a5203ffffc00f8000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail2 : optimized 5 0 s5_2 = false := by decide +kernel
private def s5_3 : State := [0x3e0003e007c00,0x39ce739ce739ce0000f83fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail3 : optimized 5 0 s5_3 = false := by decide +kernel
private def s5_4 : State := [0x801f0001f003e0,0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0xa5294a5294a529000007c0000000,0xdef7bdef7bdef7fc000000007fff]
private theorem tail4 : optimized 5 0 s5_4 = false := by decide +kernel
private def s5_5 : State := [0x801f0001f003e0,0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xe739ce739ce73903ffffc0000000]
private theorem tail5 : optimized 5 0 s5_5 = false := by decide +kernel
private def s5_6 : State := [0x801f0001f003e0,0x318c6318c6318c0000003fff8000,0x4a5294a5294a5203ffffc00f8000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail6 : optimized 5 0 s5_6 = false := by decide +kernel
private def s5_7 : State := [0x801f0001f003e0,0x39ce739ce739ce0000f83fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail7 : optimized 5 0 s5_7 = false := by decide +kernel
private def s5_8 : State := [0x842108421084200000000000000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail8 : optimized 5 0 s5_8 = false := by decide +kernel
private def s5_9 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421000000000000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail9 : optimized 5 0 s5_9 = false := by decide +kernel
private def s5_10 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xe739ce739ce73903ffffc0000000]
private theorem tail10 : optimized 5 0 s5_10 = false := by decide +kernel
private def s5_11 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc1f0001f07fff,0xa5294a5294a529000007c0000000]
private theorem tail11 : optimized 5 0 s5_11 = false := by decide +kernel
private def s5_12 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63ffe0003e007fff,0xa5294a5294a529000007c0000000]
private theorem tail12 : optimized 5 0 s5_12 = false := by decide +kernel
private def s5_13 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0xa5294a5294a529000007c0000000,0xdef7bdef7bdef7fc000000007fff]
private theorem tail13 : optimized 5 0 s5_13 = false := by decide +kernel
private def s5_14 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000,0xdef7bdef7bdef7fc000000007fff]
private theorem tail14 : optimized 5 0 s5_14 = false := by decide +kernel
private def s5_15 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0xa5294a5294a529000007c0000000,0xdef7bdef7bdef7fc000000007fff]
private theorem tail15 : optimized 5 1 s5_15 = false := by decide +kernel
private def s5_16 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003fffffe007c00,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail16 : optimized 5 0 s5_16 = false := by decide +kernel
private def s5_17 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421083ffffc1f003e0,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail17 : optimized 5 0 s5_17 = false := by decide +kernel
private def s5_18 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4a5294a5294a5203ffffc00f8000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail18 : optimized 5 0 s5_18 = false := by decide +kernel
private def s5_19 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x5294a5294a52947c00000000001f,0x739ce739ce739c03ffffffff8000,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail19 : optimized 5 0 s5_19 = false := by decide +kernel
private def s5_20 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000,0xe739ce739ce73903ffffc0000000]
private theorem tail20 : optimized 5 0 s5_20 = false := by decide +kernel
private def s5_21 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xe739ce739ce73903ffffc0000000]
private theorem tail21 : optimized 5 1 s5_21 = false := by decide +kernel
private def s5_22 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c03e0003ffffc00,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail22 : optimized 5 0 s5_22 = false := by decide +kernel
private def s5_23 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c801f003fff83e0,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail23 : optimized 5 0 s5_23 = false := by decide +kernel
private def s5_24 : State := [0x84210842108420000f8000f8000,0x39ce739ce739ce0000f83fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail24 : optimized 5 0 s5_24 = false := by decide +kernel
private def s5_25 : State := [0x318c6318c6318c0000003fff8000,0x39ce739ce739ce0000f83fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail25 : optimized 5 0 s5_25 = false := by decide +kernel
private def s5_26 : State := [0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x4a5294a5294a5203ffffc00f8000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail26 : optimized 5 0 s5_26 = false := by decide +kernel
private def s5_27 : State := [0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000,0xad6b5ad6b5ad6b0000ffc00f8000]
private theorem tail27 : optimized 5 0 s5_27 = false := by decide +kernel
private def s5_28 : State := [0x318c6318c6318c0000003fff8000,0x4a5294a5294a5203ffffc00f8000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail28 : optimized 5 1 s5_28 = false := by decide +kernel
private def s5_29 : State := [0x39ce739ce739ce0000f83fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private theorem tail29 : optimized 5 1 s5_29 = false := by decide +kernel
private def layer5 : Layer := #[s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15,s5_16,s5_17,s5_18,s5_19,s5_20,s5_21,s5_22,s5_23,s5_24,s5_25,s5_26,s5_27,s5_28,s5_29]
private def s6_0 : State := [0x3e0003e007c00,0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private def s6_1 : State := [0x801f0001f003e0,0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private def s6_2 : State := [0x84210842108420000f8000f8000,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x8c6318c6318c63fc000000007fff,0xa5294a5294a529000007c0000000]
private def layer6 : Layer := #[s6_0,s6_1,s6_2]
private def cert : Table := #[#[],#[],#[],#[],#[],layer5,layer6]
private theorem anchor5 : AtlasCut.Anchors 5 layer5 := by
  intro s mem nd
  simp only [layer5, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact AtlasCut.leaf tail12 nd
  · exact AtlasCut.leaf tail13 nd
  · exact AtlasCut.leaf tail14 nd
  · exact AtlasCut.leaf tail15 nd
  · exact AtlasCut.leaf tail16 nd
  · exact AtlasCut.leaf tail17 nd
  · exact AtlasCut.leaf tail18 nd
  · exact AtlasCut.leaf tail19 nd
  · exact AtlasCut.leaf tail20 nd
  · exact AtlasCut.leaf tail21 nd
  · exact AtlasCut.leaf tail22 nd
  · exact AtlasCut.leaf tail23 nd
  · exact AtlasCut.leaf tail24 nd
  · exact AtlasCut.leaf tail25 nd
  · exact AtlasCut.leaf tail26 nd
  · exact AtlasCut.leaf tail27 nd
  · exact AtlasCut.leaf tail28 nd
  · exact AtlasCut.leaf tail29 nd
private theorem step6_0 : stateOK layer5 6 s6_0 = true := by decide +kernel
private theorem step6_1 : stateOK layer5 6 s6_1 = true := by decide +kernel
private theorem step6_2 : stateOK layer5 6 s6_2 = true := by decide +kernel
private theorem flags6 : layer6.all (stateOK layer5 6) = true := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro s mem
  simp only [layer6, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact step6_0
  · exact step6_1
  · exact step6_2
private theorem anchor6 : AtlasCut.Anchors 6 layer6 := AtlasCut.step anchor5 flags6
theorem result : AtlasLower.lower 1126 7 :=
  AtlasCut.sound (samp := sample 1126) (k := 6) (xs := cols) cert
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) anchor6

end AtlasCutRow1126D5
