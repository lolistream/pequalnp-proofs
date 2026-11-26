import AtlasCut
import Leaves1278G0
import Leaves1278G1
import Deeper1278S17
import Deeper1278S19
import Leaves1278G4
import Leaves1278G5
import Leaves1278G6
import Leaves1278G7
import Leaves1278G8
import Leaves1278G9
import Leaves1278G10
import Leaves1278G11
import Leaves1278G12
import Leaves1278G13
import Leaves1278G14
import Leaves1278G15

namespace AtlasCutRow1278D7
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

private def cols : List W := [0xf0f0f0f0f0f0f000000000000ff,0x7070707070707000000000ffff00,0x80808080808080ffffffff000000,0x90909090909090000000000000ff,0x21212121212121000000ff000000,0x424242424242420000ff00000000,0x404040404040400ff000000ff00,0x8080808080808ff000000ff0000]
private abbrev s7_0 := CutWords1278.s0
private abbrev tail0 := CutWords1278.t0
private abbrev s7_1 := CutWords1278.s1
private abbrev tail1 := CutWords1278.t1
private abbrev s7_2 := CutWords1278.s2
private abbrev tail2 := CutWords1278.t2
private abbrev s7_3 := CutWords1278.s3
private abbrev tail3 := CutWords1278.t3
private abbrev s7_4 := CutWords1278.s4
private abbrev tail4 := CutWords1278.t4
private abbrev s7_5 := CutWords1278.s5
private abbrev tail5 := CutWords1278.t5
private abbrev s7_6 := CutWords1278.s6
private abbrev tail6 := CutWords1278.t6
private abbrev s7_7 := CutWords1278.s7
private abbrev tail7 := CutWords1278.t7
private abbrev s7_8 := CutWords1278.s8
private abbrev tail8 := CutWords1278.t8
private abbrev s7_9 := CutWords1278.s9
private abbrev tail9 := CutWords1278.t9
private abbrev s7_10 := CutWords1278.s10
private abbrev tail10 := CutWords1278.t10
private abbrev s7_11 := CutWords1278.s11
private abbrev tail11 := CutWords1278.t11
private abbrev s7_12 := CutWords1278.s12
private abbrev tail12 := CutWords1278.t12
private abbrev s7_13 := CutWords1278.s13
private abbrev tail13 := CutWords1278.t13
private abbrev s7_14 := CutWords1278.s14
private abbrev tail14 := CutWords1278.t14
private abbrev s7_15 := CutWords1278.s15
private abbrev tail15 := CutWords1278.t15
private abbrev s7_16 := CutWords1278.s16
private abbrev tail16 := CutWords1278.t16
private abbrev s7_17 := CutWords1278.s17
private abbrev tail17 := CutWords1278.node17
private abbrev s7_18 := CutWords1278.s18
private abbrev tail18 := CutWords1278.t18
private abbrev s7_19 := CutWords1278.s19
private abbrev tail19 := CutWords1278.node19
private abbrev s7_20 := CutWords1278.s20
private abbrev tail20 := CutWords1278.t20
private abbrev s7_21 := CutWords1278.s21
private abbrev tail21 := CutWords1278.t21
private abbrev s7_22 := CutWords1278.s22
private abbrev tail22 := CutWords1278.t22
private abbrev s7_23 := CutWords1278.s23
private abbrev tail23 := CutWords1278.t23
private abbrev s7_24 := CutWords1278.s24
private abbrev tail24 := CutWords1278.t24
private abbrev s7_25 := CutWords1278.s25
private abbrev tail25 := CutWords1278.t25
private abbrev s7_26 := CutWords1278.s26
private abbrev tail26 := CutWords1278.t26
private abbrev s7_27 := CutWords1278.s27
private abbrev tail27 := CutWords1278.t27
private abbrev s7_28 := CutWords1278.s28
private abbrev tail28 := CutWords1278.t28
private abbrev s7_29 := CutWords1278.s29
private abbrev tail29 := CutWords1278.t29
private abbrev s7_30 := CutWords1278.s30
private abbrev tail30 := CutWords1278.t30
private abbrev s7_31 := CutWords1278.s31
private abbrev tail31 := CutWords1278.t31
private abbrev s7_32 := CutWords1278.s32
private abbrev tail32 := CutWords1278.t32
private abbrev s7_33 := CutWords1278.s33
private abbrev tail33 := CutWords1278.t33
private abbrev s7_34 := CutWords1278.s34
private abbrev tail34 := CutWords1278.t34
private def layer7 : Layer := #[s7_0,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s7_7,s7_8,s7_9,s7_10,s7_11,s7_12,s7_13,s7_14,s7_15,s7_16,s7_17,s7_18,s7_19,s7_20,s7_21,s7_22,s7_23,s7_24,s7_25,s7_26,s7_27,s7_28,s7_29,s7_30,s7_31,s7_32,s7_33,s7_34]
private def s8_0 : State := [0x404040404040400ff000000ff00,0x8080808080808ff000000ff0000,0xf0f0f0f0f0f0f000000000000ff,0x21212121212121000000ff000000,0x424242424242420000ff00000000,0x7070707070707000000000ffff00,0x80808080808080ffffffff000000,0x90909090909090000000000000ff]
private def layer8 : Layer := #[s8_0]
private def cert : Table := #[#[],#[],#[],#[],#[],#[],#[],layer7,layer8]
private theorem anchor7 : AtlasCut.Anchors 7 layer7 := by
  intro s mem nd
  simp only [layer7, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact tail17 nd
  · exact AtlasCut.leaf tail18 nd
  · exact tail19 nd
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
  · exact AtlasCut.leaf tail31 nd
  · exact AtlasCut.leaf tail32 nd
  · exact AtlasCut.leaf tail33 nd
  · exact AtlasCut.leaf tail34 nd
private theorem flags8 : layer8.all (stateOK layer7 8) = true := by decide +kernel
private theorem anchor8 : AtlasCut.Anchors 8 layer8 := AtlasCut.step anchor7 flags8
theorem result : AtlasLower.lower 1278 9 :=
  AtlasCut.sound (samp := sample 1278) (k := 8) (xs := cols) cert
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) anchor8

end AtlasCutRow1278D7
