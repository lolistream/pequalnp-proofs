import AtlasCut

namespace AtlasCutRow3242D6
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

private def cols : List W := [0xc30c30c30c30c3c000000003ffff,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x14514514514514c000000000003f,0x6186186186186100000000fc0000,0x82082082082080003f000000fc0,0x8208208208208200fc003f000000,0x3f000fc003f000]
private def s6_0 : State := [0x3f000fc003f000,0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x6186186186186100000000fc0000,0xb2cb2cb2cb2cb23ffff03f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail0 : optimized 6 0 s6_0 = false := by decide +kernel
private def s6_1 : State := [0x3f000fc003f000,0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xd75d75d75d75d7c000000003ffff]
private theorem tail1 : optimized 6 0 s6_1 = false := by decide +kernel
private def s6_2 : State := [0x3f000fc003f000,0x82082082082080003f000000fc0,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8e38e38e38e38e00fc0ffffc0000,0xc30c30c30c30c3c000000003ffff]
private theorem tail2 : optimized 6 0 s6_2 = false := by decide +kernel
private def s6_3 : State := [0x3f000fc003f000,0x82082082082080003f000000fc0,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6db6db6db6db6d00000ffffc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail3 : optimized 6 0 s6_3 = false := by decide +kernel
private def s6_4 : State := [0x3f000fc003f000,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xcb2cb2cb2cb2cbc003f00003ffff]
private theorem tail4 : optimized 6 0 s6_4 = false := by decide +kernel
private def s6_5 : State := [0x3f000fc003f000,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x38e38e38e38e383ffff000000fc0,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail5 : optimized 6 0 s6_5 = false := by decide +kernel
private def s6_6 : State := [0x820820820820800000000000000,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail6 : optimized 6 0 s6_6 = false := by decide +kernel
private def s6_7 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200000000000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail7 : optimized 6 0 s6_7 = false := by decide +kernel
private def s6_8 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3ff000fc003ffff]
private theorem tail8 : optimized 6 0 s6_8 = false := by decide +kernel
private def s6_9 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xcb2cb2cb2cb2cbc003f00003ffff]
private theorem tail9 : optimized 6 0 s6_9 = false := by decide +kernel
private def s6_10 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xd75d75d75d75d7c000000003ffff]
private theorem tail10 : optimized 6 0 s6_10 = false := by decide +kernel
private def s6_11 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8e38e38e38e38e00fc0ffffc0000,0xc30c30c30c30c3c000000003ffff]
private theorem tail11 : optimized 6 0 s6_11 = false := by decide +kernel
private def s6_12 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0xb2cb2cb2cb2cb23ffff03f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail12 : optimized 6 0 s6_12 = false := by decide +kernel
private def s6_13 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0xc30c30c30c30c3c000000003ffff,0xe38e38e38e38e300fc003ffc0000]
private theorem tail13 : optimized 6 0 s6_13 = false := by decide +kernel
private def s6_14 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6db6db6db6db6d00000ffffc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail14 : optimized 6 0 s6_14 = false := by decide +kernel
private def s6_15 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303fffffc003f000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail15 : optimized 6 0 s6_15 = false := by decide +kernel
private def s6_16 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x38e38e38e38e383ffff000000fc0,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail16 : optimized 6 0 s6_16 = false := by decide +kernel
private def s6_17 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xb2cb2cb2cb2cb23ffff03f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail17 : optimized 6 0 s6_17 = false := by decide +kernel
private def s6_18 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x6186186186186100000000fc0000,0xb2cb2cb2cb2cb23ffff03f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail18 : optimized 6 1 s6_18 = false := by decide +kernel
private def s6_19 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff,0xd75d75d75d75d7c000000003ffff]
private theorem tail19 : optimized 6 0 s6_19 = false := by decide +kernel
private def s6_20 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xd75d75d75d75d7c000000003ffff]
private theorem tail20 : optimized 6 1 s6_20 = false := by decide +kernel
private def s6_21 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c3f000ffffff000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail21 : optimized 6 0 s6_21 = false := by decide +kernel
private def s6_22 : State := [0x82082082082080003f000000fc0,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x6db6db6db6db6d00000ffffc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail22 : optimized 6 0 s6_22 = false := by decide +kernel
private def s6_23 : State := [0x82082082082080003f000000fc0,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0x8e38e38e38e38e00fc0ffffc0000,0xc30c30c30c30c3c000000003ffff]
private theorem tail23 : optimized 6 0 s6_23 = false := by decide +kernel
private def s6_24 : State := [0x82082082082080003f000000fc0,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8e38e38e38e38e00fc0ffffc0000,0xc30c30c30c30c3c000000003ffff]
private theorem tail24 : optimized 6 1 s6_24 = false := by decide +kernel
private def s6_25 : State := [0x82082082082080003f000000fc0,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6db6db6db6db6d00000ffffc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail25 : optimized 6 1 s6_25 = false := by decide +kernel
private def s6_26 : State := [0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x1c71c71c71c71cc003f000000fff,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail26 : optimized 6 0 s6_26 = false := by decide +kernel
private def s6_27 : State := [0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x38e38e38e38e383ffff000000fc0,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail27 : optimized 6 0 s6_27 = false := by decide +kernel
private def s6_28 : State := [0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff,0xcb2cb2cb2cb2cbc003f00003ffff]
private theorem tail28 : optimized 6 0 s6_28 = false := by decide +kernel
private def s6_29 : State := [0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xcb2cb2cb2cb2cbc003f00003ffff]
private theorem tail29 : optimized 6 1 s6_29 = false := by decide +kernel
private def s6_30 : State := [0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x38e38e38e38e383ffff000000fc0,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private theorem tail30 : optimized 6 1 s6_30 = false := by decide +kernel
private def layer6 : Layer := #[s6_0,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s6_7,s6_8,s6_9,s6_10,s6_11,s6_12,s6_13,s6_14,s6_15,s6_16,s6_17,s6_18,s6_19,s6_20,s6_21,s6_22,s6_23,s6_24,s6_25,s6_26,s6_27,s6_28,s6_29,s6_30]
private def s7_0 : State := [0x3f000fc003f000,0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private def s7_1 : State := [0x82082082082080003f000000fc0,0xc30c30c30c30c00000ffffc0000,0x14514514514514c000000000003f,0x30c30c30c30c303ffff000000000,0x6186186186186100000000fc0000,0x8208208208208200fc003f000000,0xc30c30c30c30c3c000000003ffff]
private def layer7 : Layer := #[s7_0,s7_1]
private def cert : Table := #[#[],#[],#[],#[],#[],#[],layer6,layer7]
private theorem anchor6 : AtlasCut.Anchors 6 layer6 := by
  intro s mem nd
  simp only [layer6, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact AtlasCut.leaf tail30 nd
private theorem step7_0 : stateOK layer6 7 s7_0 = true := by decide +kernel
private theorem step7_1 : stateOK layer6 7 s7_1 = true := by decide +kernel
private theorem flags7 : layer7.all (stateOK layer6 7) = true := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro s mem
  simp only [layer7, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact step7_0
  · exact step7_1
private theorem anchor7 : AtlasCut.Anchors 7 layer7 := AtlasCut.step anchor6 flags7
theorem result : AtlasLower.lower 3242 8 :=
  AtlasCut.sound (samp := sample 3242) (k := 7) (xs := cols) cert
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) anchor7

end AtlasCutRow3242D6
