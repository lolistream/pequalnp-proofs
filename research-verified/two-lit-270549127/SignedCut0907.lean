import Case24992
import SignedLeaf031
import SignedLeaf050
import SignedLeaf056
import SignedLeaf066
import SignedLeaf067
import SignedLeaf088
import SignedLeaf110
import SignedLeaf111
import SignedLeaf112
import SignedLeaf117

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0907 : List Sig := [(0x0, 0x20008002000800200080020008), (0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0907 : List (List Sig) := [sC0622, sC0745, sC0786, sC0908, sC0909, sC0910, sC0911]
private def bC0907 : List (List Sig) := [sC0912, sC0913, sC0914, sC0915, sC0916, sC0917, sC0918]
theorem qC0907 : Impossible 8 2 sC0907 := by
  apply cut (us := aC0907) (bs := bC0907) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC0907, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0622
    · exact qC0745
    · exact qC0786
    · exact qC0908
    · exact qC0909
    · exact qC0910
    · exact qC0911
  · intro x hx
    simp only [bC0907, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0912
    · exact qC0913
    · exact qC0914
    · exact qC0915
    · exact qC0916
    · exact qC0917
    · exact qC0918

end Lower24992
