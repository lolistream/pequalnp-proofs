import Case24992
import SignedLeaf057
import SignedLeaf068
import SignedLeaf070
import SignedLeaf074
import SignedLeaf081
import SignedLeaf093
import SignedLeaf115
import SignedLeaf123
import SignedLeaf130

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0057 : List Sig := [(0x0, 0x20008002000800200080020008), (0x0, 0x2913a44e913a44e913a44e913a44), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc0000000000ffffffffffffff, 0x1fc07f01fc07f01fc07f01fc07f)]
private def aC0057 : List (List Sig) := []
private def bC0057 : List (List Sig) := [sC0058, sC0059, sC0060, sC0014, sC0061, sC0027, sC0062, sC0063, sC0046, sC0064, sC0065, sC0066, sC0067, sC0068, sC0069, sC0070]
theorem qC0057 : Impossible 7 1 sC0057 := by
  apply cut (us := aC0057) (bs := bC0057) (by decide +kernel)
  · decide +kernel
  · simp [aC0057]
  · intro x hx
    simp only [bC0057, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0058
    · exact qC0059
    · exact qC0060
    · exact qC0014
    · exact qC0061
    · exact qC0027
    · exact qC0062
    · exact qC0063
    · exact qC0046
    · exact qC0064
    · exact qC0065
    · exact qC0066
    · exact qC0067
    · exact qC0068
    · exact qC0069
    · exact qC0070

end Lower24992
