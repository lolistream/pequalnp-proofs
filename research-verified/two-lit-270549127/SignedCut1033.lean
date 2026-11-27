import Case24992
import SignedLeaf065
import SignedLeaf066
import SignedLeaf069
import SignedLeaf076
import SignedLeaf082
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

def sC1033 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0x2f33bccef33bccef33bccef33bcc), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC1033 : List (List Sig) := [sC0658, sC0687, sC1034, sC1035, sC1036, sC1037, sC0728, sC0778, sC0818, sC1038, sC0900, sC0740]
private def bC1033 : List (List Sig) := [sC0962, sC0982, sC1039, sC1008, sC1024, sC0941, sC1040, sC1041, sC1042, sC1043, sC1044, sC1016, sC1031, sC1045]
theorem qC1033 : Impossible 8 2 sC1033 := by
  apply cut (us := aC1033) (bs := bC1033) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC1033, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0658
    · exact qC0687
    · exact qC1034
    · exact qC1035
    · exact qC1036
    · exact qC1037
    · exact qC0728
    · exact qC0778
    · exact qC0818
    · exact qC1038
    · exact qC0900
    · exact qC0740
  · intro x hx
    simp only [bC1033, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0962
    · exact qC0982
    · exact qC1039
    · exact qC1008
    · exact qC1024
    · exact qC0941
    · exact qC1040
    · exact qC1041
    · exact qC1042
    · exact qC1043
    · exact qC1044
    · exact qC1016
    · exact qC1031
    · exact qC1045

end Lower24992
