import Case24992
import SignedLeaf020
import SignedLeaf021
import SignedLeaf022
import SignedLeaf023
import SignedLeaf026
import SignedLeaf027
import SignedLeaf028
import SignedLeaf035
import SignedLeaf036
import SignedLeaf042
import SignedLeaf043
import SignedLeaf046
import SignedLeaf057
import SignedLeaf085
import SignedLeaf120

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC1078 : List Sig := [(0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x0, 0x2913a44e913a44e913a44e913a44)]
private def aC1078 : List (List Sig) := [sC1079, sC1080, sC1081, sC1082, sC1083, sC1084, sC1085, sC1086, sC1087, sC1088, sC1089, sC1090]
private def bC1078 : List (List Sig) := [sC1091, sC1092, sC1093, sC1094, sC1095, sC1096, sC1097, sC1098, sC1099]
theorem qC1078 : Impossible 9 3 sC1078 := by
  apply cut (us := aC1078) (bs := bC1078) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC1078, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC1079
    · exact qC1080
    · exact qC1081
    · exact qC1082
    · exact qC1083
    · exact qC1084
    · exact qC1085
    · exact qC1086
    · exact qC1087
    · exact qC1088
    · exact qC1089
    · exact qC1090
  · intro x hx
    simp only [bC1078, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC1091
    · exact qC1092
    · exact qC1093
    · exact qC1094
    · exact qC1095
    · exact qC1096
    · exact qC1097
    · exact qC1098
    · exact qC1099

end Lower24992
