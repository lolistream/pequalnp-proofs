import Case24992
import SignedLeaf017
import SignedLeaf018
import SignedLeaf019
import SignedLeaf046
import SignedLeaf064
import SignedLeaf068
import SignedLeaf071
import SignedLeaf093
import SignedLeaf098
import SignedLeaf099
import SignedLeaf100
import SignedLeaf101
import SignedLeaf105
import SignedLeaf107
import SignedLeaf117
import SignedLeaf118
import SignedLeaf120

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0951 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x291fa47e91fa47e91fa47e91fa47)]
private def aC0951 : List (List Sig) := [sC0952, sC0953, sC0954, sC0955, sC0956, sC0957, sC0723, sC0774, sC0814, sC0856, sC0896, sC0737]
private def bC0951 : List (List Sig) := [sC0958, sC0959, sC0960, sC0961, sC0962, sC0963, sC0964, sC0965, sC0966, sC0967, sC0968, sC0969]
theorem qC0951 : Impossible 8 2 sC0951 := by
  apply cut (us := aC0951) (bs := bC0951) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC0951, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0952
    · exact qC0953
    · exact qC0954
    · exact qC0955
    · exact qC0956
    · exact qC0957
    · exact qC0723
    · exact qC0774
    · exact qC0814
    · exact qC0856
    · exact qC0896
    · exact qC0737
  · intro x hx
    simp only [bC0951, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0958
    · exact qC0959
    · exact qC0960
    · exact qC0961
    · exact qC0962
    · exact qC0963
    · exact qC0964
    · exact qC0965
    · exact qC0966
    · exact qC0967
    · exact qC0968
    · exact qC0969

end Lower24992
