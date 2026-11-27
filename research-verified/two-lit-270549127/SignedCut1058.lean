import Case24992
import SignedLeaf065
import SignedLeaf067
import SignedLeaf076
import SignedLeaf083
import SignedLeaf084
import SignedLeaf086
import SignedLeaf089
import SignedLeaf090
import SignedLeaf093
import SignedLeaf094
import SignedLeaf095
import SignedLeaf096
import SignedLeaf105
import SignedLeaf107
import SignedLeaf117
import SignedLeaf118

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC1058 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x29f3a7ce9f3a7ce9f3a7ce9f3a7c), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC1058 : List (List Sig) := [sC0659, sC0690, sC1059, sC1060, sC1061, sC1062, sC0730, sC0780, sC0820, sC0860, sC1063, sC0741]
private def bC1058 : List (List Sig) := [sC0964, sC1064, sC1000, sC1010, sC1026, sC1040, sC1056, sC0943, sC1065, sC1066, sC1067, sC1017, sC1032, sC1045]
theorem qC1058 : Impossible 8 2 sC1058 := by
  apply cut (us := aC1058) (bs := bC1058) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC1058, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0659
    · exact qC0690
    · exact qC1059
    · exact qC1060
    · exact qC1061
    · exact qC1062
    · exact qC0730
    · exact qC0780
    · exact qC0820
    · exact qC0860
    · exact qC1063
    · exact qC0741
  · intro x hx
    simp only [bC1058, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0964
    · exact qC1064
    · exact qC1000
    · exact qC1010
    · exact qC1026
    · exact qC1040
    · exact qC1056
    · exact qC0943
    · exact qC1065
    · exact qC1066
    · exact qC1067
    · exact qC1017
    · exact qC1032
    · exact qC1045

end Lower24992
