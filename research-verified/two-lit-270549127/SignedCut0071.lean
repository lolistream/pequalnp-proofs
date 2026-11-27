import Case24992
import SignedLeaf057
import SignedLeaf067
import SignedLeaf068
import SignedLeaf070
import SignedLeaf072
import SignedLeaf074
import SignedLeaf075
import SignedLeaf081
import SignedLeaf082
import SignedLeaf105
import SignedLeaf123
import SignedLeaf130

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0071 : List Sig := [(0x0, 0x20008002000800200080020008), (0x0, 0x2913a44e913a44e913a44e913a44), (0x3fffffffffffffc000, 0xfe03f80fe03f80fe03f80fe03f8), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0071 : List (List Sig) := []
private def bC0071 : List (List Sig) := [sC0072, sC0073, sC0074, sC0075, sC0015, sC0076, sC0028, sC0077, sC0078, sC0046, sC0079, sC0080, sC0081, sC0082, sC0083, sC0084, sC0085, sC0086]
theorem qC0071 : Impossible 7 1 sC0071 := by
  apply cut (us := aC0071) (bs := bC0071) (by decide +kernel)
  · decide +kernel
  · simp [aC0071]
  · intro x hx
    simp only [bC0071, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0072
    · exact qC0073
    · exact qC0074
    · exact qC0075
    · exact qC0015
    · exact qC0076
    · exact qC0028
    · exact qC0077
    · exact qC0078
    · exact qC0046
    · exact qC0079
    · exact qC0080
    · exact qC0081
    · exact qC0082
    · exact qC0083
    · exact qC0084
    · exact qC0085
    · exact qC0086

end Lower24992
