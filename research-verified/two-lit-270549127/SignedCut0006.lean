import Case24992
import SignedCut0012
import SignedCut0025
import SignedCut0039
import SignedCut0057
import SignedCut0071
import SignedCut0088
import SignedLeaf002
import SignedLeaf003
import SignedLeaf004
import SignedLeaf007
import SignedLeaf008
import SignedLeaf011
import SignedLeaf047
import SignedLeaf061
import SignedLeaf069
import SignedLeaf083
import SignedLeaf098
import SignedLeaf099
import SignedLeaf101
import SignedLeaf117
import SignedLeaf123

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0006 : List Sig := [(0x0, 0x20008002000800200080020008), (0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0006 : List (List Sig) := []
private def bC0006 : List (List Sig) := [sC0007, sC0008, sC0009, sC0010, sC0011, sC0012, sC0024, sC0025, sC0036, sC0037, sC0038, sC0039, sC0054, sC0055, sC0056, sC0057, sC0071, sC0087, sC0088, sC0095, sC0096, sC0097, sC0098, sC0099, sC0100, sC0101]
theorem qC0006 : Impossible 8 1 sC0006 := by
  apply cut (us := aC0006) (bs := bC0006) (by decide +kernel)
  · decide +kernel
  · simp [aC0006]
  · intro x hx
    simp only [bC0006, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0007
    · exact qC0008
    · exact qC0009
    · exact qC0010
    · exact qC0011
    · exact qC0012
    · exact qC0024
    · exact qC0025
    · exact qC0036
    · exact qC0037
    · exact qC0038
    · exact qC0039
    · exact qC0054
    · exact qC0055
    · exact qC0056
    · exact qC0057
    · exact qC0071
    · exact qC0087
    · exact qC0088
    · exact qC0095
    · exact qC0096
    · exact qC0097
    · exact qC0098
    · exact qC0099
    · exact qC0100
    · exact qC0101

end Lower24992
