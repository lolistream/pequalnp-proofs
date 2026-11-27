import Case24992
import SignedLeaf043
import SignedLeaf044
import SignedLeaf045
import SignedLeaf070
import SignedLeaf071
import SignedLeaf072
import SignedLeaf088
import SignedLeaf123

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0088 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0x0, 0x2933a4ce933a4ce933a4ce933a4c), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0088 : List (List Sig) := []
private def bC0088 : List (List Sig) := [sC0048, sC0065, sC0080, sC0089, sC0021, sC0034, sC0090, sC0091, sC0092, sC0023, sC0035, sC0093, sC0094]
theorem qC0088 : Impossible 7 1 sC0088 := by
  apply cut (us := aC0088) (bs := bC0088) (by decide +kernel)
  · decide +kernel
  · simp [aC0088]
  · intro x hx
    simp only [bC0088, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0048
    · exact qC0065
    · exact qC0080
    · exact qC0089
    · exact qC0021
    · exact qC0034
    · exact qC0090
    · exact qC0091
    · exact qC0092
    · exact qC0023
    · exact qC0035
    · exact qC0093
    · exact qC0094

end Lower24992
