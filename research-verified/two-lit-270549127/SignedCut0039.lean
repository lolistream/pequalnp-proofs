import Case24992
import SignedLeaf057
import SignedLeaf067
import SignedLeaf068
import SignedLeaf070
import SignedLeaf071
import SignedLeaf074
import SignedLeaf081
import SignedLeaf085
import SignedLeaf092
import SignedLeaf107
import SignedLeaf115
import SignedLeaf123

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0039 : List Sig := [(0x0, 0x20008002000800200080020008), (0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc0000003fff0003ffffffffff, 0xe3c38f0e3c38f0e3c38f0e3c38f)]
private def aC0039 : List (List Sig) := []
private def bC0039 : List (List Sig) := [sC0040, sC0041, sC0042, sC0013, sC0043, sC0026, sC0044, sC0045, sC0046, sC0047, sC0048, sC0049, sC0050, sC0051, sC0052, sC0053]
theorem qC0039 : Impossible 7 1 sC0039 := by
  apply cut (us := aC0039) (bs := bC0039) (by decide +kernel)
  · decide +kernel
  · simp [aC0039]
  · intro x hx
    simp only [bC0039, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0040
    · exact qC0041
    · exact qC0042
    · exact qC0013
    · exact qC0043
    · exact qC0026
    · exact qC0044
    · exact qC0045
    · exact qC0046
    · exact qC0047
    · exact qC0048
    · exact qC0049
    · exact qC0050
    · exact qC0051
    · exact qC0052
    · exact qC0053

end Lower24992
