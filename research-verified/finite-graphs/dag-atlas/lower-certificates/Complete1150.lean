import AtlasCut
import Leaves1150G0
import Deeper1150S16
import Leaves1150G2
import Deeper1150S23
import Leaves1150G4
import Deeper1150S30
import Deeper1150S31
import Leaves1150G7
import Deeper1150S38
import Deeper1150S39
import Deeper1150S40
import Leaves1150G11
import Leaves1150G12
import Leaves1150G13
import Leaves1150G14
import Leaves1150G15
import Leaves1150G16
import Leaves1150G17
import Leaves1150G18

namespace AtlasCutRow1150D7
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

private def cols : List W := [0x1e3c78f1e3c78f0000000000007f,0x60c183060c18300000000fffff80,0x81020408102040fffffff0000000,0xa142850a1428500000000000007f,0x42850a142850a1000007f0000000,0x40810204081020003f800003f80,0x810204081020401fc00001fc000,0x10204081020408fe00000fe00000]
private abbrev s7_0 := CutWords1150.s0
private abbrev tail0 := CutWords1150.t0
private abbrev s7_1 := CutWords1150.s1
private abbrev tail1 := CutWords1150.t1
private abbrev s7_2 := CutWords1150.s2
private abbrev tail2 := CutWords1150.t2
private abbrev s7_3 := CutWords1150.s3
private abbrev tail3 := CutWords1150.t3
private abbrev s7_4 := CutWords1150.s4
private abbrev tail4 := CutWords1150.t4
private abbrev s7_5 := CutWords1150.s5
private abbrev tail5 := CutWords1150.t5
private abbrev s7_6 := CutWords1150.s6
private abbrev tail6 := CutWords1150.t6
private abbrev s7_7 := CutWords1150.s7
private abbrev tail7 := CutWords1150.t7
private abbrev s7_8 := CutWords1150.s8
private abbrev tail8 := CutWords1150.t8
private abbrev s7_9 := CutWords1150.s9
private abbrev tail9 := CutWords1150.t9
private abbrev s7_10 := CutWords1150.s10
private abbrev tail10 := CutWords1150.t10
private abbrev s7_11 := CutWords1150.s11
private abbrev tail11 := CutWords1150.t11
private abbrev s7_12 := CutWords1150.s12
private abbrev tail12 := CutWords1150.t12
private abbrev s7_13 := CutWords1150.s13
private abbrev tail13 := CutWords1150.t13
private abbrev s7_14 := CutWords1150.s14
private abbrev tail14 := CutWords1150.t14
private abbrev s7_15 := CutWords1150.s15
private abbrev tail15 := CutWords1150.t15
private abbrev s7_16 := CutWords1150.s16
private abbrev tail16 := CutWords1150.node16
private abbrev s7_17 := CutWords1150.s17
private abbrev tail17 := CutWords1150.t17
private abbrev s7_18 := CutWords1150.s18
private abbrev tail18 := CutWords1150.t18
private abbrev s7_19 := CutWords1150.s19
private abbrev tail19 := CutWords1150.t19
private abbrev s7_20 := CutWords1150.s20
private abbrev tail20 := CutWords1150.t20
private abbrev s7_21 := CutWords1150.s21
private abbrev tail21 := CutWords1150.t21
private abbrev s7_22 := CutWords1150.s22
private abbrev tail22 := CutWords1150.t22
private abbrev s7_23 := CutWords1150.s23
private abbrev tail23 := CutWords1150.node23
private abbrev s7_24 := CutWords1150.s24
private abbrev tail24 := CutWords1150.t24
private abbrev s7_25 := CutWords1150.s25
private abbrev tail25 := CutWords1150.t25
private abbrev s7_26 := CutWords1150.s26
private abbrev tail26 := CutWords1150.t26
private abbrev s7_27 := CutWords1150.s27
private abbrev tail27 := CutWords1150.t27
private abbrev s7_28 := CutWords1150.s28
private abbrev tail28 := CutWords1150.t28
private abbrev s7_29 := CutWords1150.s29
private abbrev tail29 := CutWords1150.t29
private abbrev s7_30 := CutWords1150.s30
private abbrev tail30 := CutWords1150.node30
private abbrev s7_31 := CutWords1150.s31
private abbrev tail31 := CutWords1150.node31
private abbrev s7_32 := CutWords1150.s32
private abbrev tail32 := CutWords1150.t32
private abbrev s7_33 := CutWords1150.s33
private abbrev tail33 := CutWords1150.t33
private abbrev s7_34 := CutWords1150.s34
private abbrev tail34 := CutWords1150.t34
private abbrev s7_35 := CutWords1150.s35
private abbrev tail35 := CutWords1150.t35
private abbrev s7_36 := CutWords1150.s36
private abbrev tail36 := CutWords1150.t36
private abbrev s7_37 := CutWords1150.s37
private abbrev tail37 := CutWords1150.t37
private abbrev s7_38 := CutWords1150.s38
private abbrev tail38 := CutWords1150.node38
private abbrev s7_39 := CutWords1150.s39
private abbrev tail39 := CutWords1150.node39
private abbrev s7_40 := CutWords1150.s40
private abbrev tail40 := CutWords1150.node40
private def layer7 : Layer := #[s7_0,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s7_7,s7_8,s7_9,s7_10,s7_11,s7_12,s7_13,s7_14,s7_15,s7_16,s7_17,s7_18,s7_19,s7_20,s7_21,s7_22,s7_23,s7_24,s7_25,s7_26,s7_27,s7_28,s7_29,s7_30,s7_31,s7_32,s7_33,s7_34,s7_35,s7_36,s7_37,s7_38,s7_39,s7_40]
private def s8_0 : State := [0x40810204081020003f800003f80,0x810204081020401fc00001fc000,0x10204081020408fe00000fe00000,0x1e3c78f1e3c78f0000000000007f,0x42850a142850a1000007f0000000,0x60c183060c18300000000fffff80,0x81020408102040fffffff0000000,0xa142850a1428500000000000007f]
private def layer8 : Layer := #[s8_0]
private def cert : Table := #[#[],#[],#[],#[],#[],#[],#[],layer7,layer8]
private theorem anchor7 : AtlasCut.Anchors 7 layer7 := by
  intro s mem nd
  simp only [layer7, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact tail16 nd
  · exact AtlasCut.leaf tail17 nd
  · exact AtlasCut.leaf tail18 nd
  · exact AtlasCut.leaf tail19 nd
  · exact AtlasCut.leaf tail20 nd
  · exact AtlasCut.leaf tail21 nd
  · exact AtlasCut.leaf tail22 nd
  · exact tail23 nd
  · exact AtlasCut.leaf tail24 nd
  · exact AtlasCut.leaf tail25 nd
  · exact AtlasCut.leaf tail26 nd
  · exact AtlasCut.leaf tail27 nd
  · exact AtlasCut.leaf tail28 nd
  · exact AtlasCut.leaf tail29 nd
  · exact tail30 nd
  · exact tail31 nd
  · exact AtlasCut.leaf tail32 nd
  · exact AtlasCut.leaf tail33 nd
  · exact AtlasCut.leaf tail34 nd
  · exact AtlasCut.leaf tail35 nd
  · exact AtlasCut.leaf tail36 nd
  · exact AtlasCut.leaf tail37 nd
  · exact tail38 nd
  · exact tail39 nd
  · exact tail40 nd
private theorem flags8 : layer8.all (stateOK layer7 8) = true := by decide +kernel
private theorem anchor8 : AtlasCut.Anchors 8 layer8 := AtlasCut.step anchor7 flags8
theorem result : AtlasLower.lower 1150 9 :=
  AtlasCut.sound (samp := sample 1150) (k := 8) (xs := cols) cert
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) anchor8

end AtlasCutRow1150D7
