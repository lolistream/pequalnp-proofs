import Case24992
import SignedLeaf023
import SignedLeaf069
import SignedLeaf083
import SignedLeaf086
import SignedLeaf087
import SignedLeaf095
import SignedLeaf096
import SignedLeaf105
import SignedLeaf109
import SignedLeaf111
import SignedLeaf112
import SignedLeaf117
import SignedLeaf118
import SignedLeaf130
import SignedLeaf133

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC1068 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffc0000000000ffffffffffffff, 0x1fc07f01fc07f01fc07f01fc07f)]
private def aC1068 : List (List Sig) := [sC1069, sC1070, sC0691, sC0692, sC1071, sC1072, sC1073, sC0731, sC0781, sC0821, sC0861, sC1074]
private def bC1068 : List (List Sig) := [sC1075, sC0943, sC0944, sC1076, sC1077, sC1011, sC1027, sC1041, sC1057]
theorem qC1068 : Impossible 8 2 sC1068 := by
  apply cut (us := aC1068) (bs := bC1068) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC1068, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC1069
    · exact qC1070
    · exact qC0691
    · exact qC0692
    · exact qC1071
    · exact qC1072
    · exact qC1073
    · exact qC0731
    · exact qC0781
    · exact qC0821
    · exact qC0861
    · exact qC1074
  · intro x hx
    simp only [bC1068, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC1075
    · exact qC0943
    · exact qC0944
    · exact qC1076
    · exact qC1077
    · exact qC1011
    · exact qC1027
    · exact qC1041
    · exact qC1057

end Lower24992
