import AtlasCut
import Deeper3324S10
import Leaves3324G1
import Deeper3324S17
import Deeper3324S18
import Leaves3324G4
import Leaves3324G5
import Leaves3324G6
import Leaves3324G7
import Leaves3324G8
import Leaves3324G9
import Leaves3324G10
import Leaves3324G11
import Leaves3324G12
import Leaves3324G13
import Leaves3324G14

namespace AtlasCutRow3324D7
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

private def cols : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x48484848484848000000000000ff,0x909090909090900000000000ff00,0x212121212121210000ff00000000,0x202020202020200ff0000ff0000,0x4040404040404ff0000ff000000]
private abbrev s7_0 := CutWords3324.s0
private abbrev tail0 := CutWords3324.t0
private abbrev s7_1 := CutWords3324.s1
private abbrev tail1 := CutWords3324.t1
private abbrev s7_2 := CutWords3324.s2
private abbrev tail2 := CutWords3324.t2
private abbrev s7_3 := CutWords3324.s3
private abbrev tail3 := CutWords3324.t3
private abbrev s7_4 := CutWords3324.s4
private abbrev tail4 := CutWords3324.t4
private abbrev s7_5 := CutWords3324.s5
private abbrev tail5 := CutWords3324.t5
private abbrev s7_6 := CutWords3324.s6
private abbrev tail6 := CutWords3324.t6
private abbrev s7_7 := CutWords3324.s7
private abbrev tail7 := CutWords3324.t7
private abbrev s7_8 := CutWords3324.s8
private abbrev tail8 := CutWords3324.t8
private abbrev s7_9 := CutWords3324.s9
private abbrev tail9 := CutWords3324.t9
private abbrev s7_10 := CutWords3324.s10
private abbrev tail10 := CutWords3324.node10
private abbrev s7_11 := CutWords3324.s11
private abbrev tail11 := CutWords3324.t11
private abbrev s7_12 := CutWords3324.s12
private abbrev tail12 := CutWords3324.t12
private abbrev s7_13 := CutWords3324.s13
private abbrev tail13 := CutWords3324.t13
private abbrev s7_14 := CutWords3324.s14
private abbrev tail14 := CutWords3324.t14
private abbrev s7_15 := CutWords3324.s15
private abbrev tail15 := CutWords3324.t15
private abbrev s7_16 := CutWords3324.s16
private abbrev tail16 := CutWords3324.t16
private abbrev s7_17 := CutWords3324.s17
private abbrev tail17 := CutWords3324.node17
private abbrev s7_18 := CutWords3324.s18
private abbrev tail18 := CutWords3324.node18
private abbrev s7_19 := CutWords3324.s19
private abbrev tail19 := CutWords3324.t19
private abbrev s7_20 := CutWords3324.s20
private abbrev tail20 := CutWords3324.t20
private abbrev s7_21 := CutWords3324.s21
private abbrev tail21 := CutWords3324.t21
private abbrev s7_22 := CutWords3324.s22
private abbrev tail22 := CutWords3324.t22
private abbrev s7_23 := CutWords3324.s23
private abbrev tail23 := CutWords3324.t23
private abbrev s7_24 := CutWords3324.s24
private abbrev tail24 := CutWords3324.t24
private abbrev s7_25 := CutWords3324.s25
private abbrev tail25 := CutWords3324.t25
private abbrev s7_26 := CutWords3324.s26
private abbrev tail26 := CutWords3324.t26
private abbrev s7_27 := CutWords3324.s27
private abbrev tail27 := CutWords3324.t27
private abbrev s7_28 := CutWords3324.s28
private abbrev tail28 := CutWords3324.t28
private abbrev s7_29 := CutWords3324.s29
private abbrev tail29 := CutWords3324.t29
private abbrev s7_30 := CutWords3324.s30
private abbrev tail30 := CutWords3324.t30
private abbrev s7_31 := CutWords3324.s31
private abbrev tail31 := CutWords3324.t31
private def layer7 : Layer := #[s7_0,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s7_7,s7_8,s7_9,s7_10,s7_11,s7_12,s7_13,s7_14,s7_15,s7_16,s7_17,s7_18,s7_19,s7_20,s7_21,s7_22,s7_23,s7_24,s7_25,s7_26,s7_27,s7_28,s7_29,s7_30,s7_31]
private def s8_0 : State := [0x202020202020200ff0000ff0000,0x4040404040404ff0000ff000000,0x70707070707070000000000ffff,0x212121212121210000ff00000000,0x38383838383838000000ffff0000,0x48484848484848000000000000ff,0x909090909090900000000000ff00,0xc0c0c0c0c0c0c0ffffff00000000]
private def layer8 : Layer := #[s8_0]
private def cert : Table := #[#[],#[],#[],#[],#[],#[],#[],layer7,layer8]
private theorem anchor7 : AtlasCut.Anchors 7 layer7 := by
  intro s mem nd
  simp only [layer7, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact tail10 nd
  · exact AtlasCut.leaf tail11 nd
  · exact AtlasCut.leaf tail12 nd
  · exact AtlasCut.leaf tail13 nd
  · exact AtlasCut.leaf tail14 nd
  · exact AtlasCut.leaf tail15 nd
  · exact AtlasCut.leaf tail16 nd
  · exact tail17 nd
  · exact tail18 nd
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
  · exact AtlasCut.leaf tail31 nd
private theorem flags8 : layer8.all (stateOK layer7 8) = true := by decide +kernel
private theorem anchor8 : AtlasCut.Anchors 8 layer8 := AtlasCut.step anchor7 flags8
theorem result : AtlasLower.lower 3324 9 :=
  AtlasCut.sound (samp := sample 3324) (k := 8) (xs := cols) cert
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) anchor8

end AtlasCutRow3324D7
