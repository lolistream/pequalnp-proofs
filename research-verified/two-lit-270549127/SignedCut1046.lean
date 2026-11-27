import Case24992
import SignedLeaf022
import SignedLeaf069
import SignedLeaf083
import SignedLeaf086
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

def sC1046 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffc0000003fff0003ffffffffff, 0xe3c38f0e3c38f0e3c38f0e3c38f)]
private def aC1046 : List (List Sig) := [sC1047, sC1048, sC0688, sC0689, sC1049, sC1050, sC1051, sC0729, sC0779, sC0819, sC0901, sC1052]
private def bC1046 : List (List Sig) := [sC1053, sC0941, sC0942, sC1054, sC1055, sC1009, sC1025, sC1056, sC1057]
theorem qC1046 : Impossible 8 2 sC1046 := by
  apply cut (us := aC1046) (bs := bC1046) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC1046, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC1047
    · exact qC1048
    · exact qC0688
    · exact qC0689
    · exact qC1049
    · exact qC1050
    · exact qC1051
    · exact qC0729
    · exact qC0779
    · exact qC0819
    · exact qC0901
    · exact qC1052
  · intro x hx
    simp only [bC1046, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC1053
    · exact qC0941
    · exact qC0942
    · exact qC1054
    · exact qC1055
    · exact qC1009
    · exact qC1025
    · exact qC1056
    · exact qC1057

end Lower24992
