import Case24992
import SignedLeaf012
import SignedLeaf051
import SignedLeaf058
import SignedLeaf062
import SignedLeaf066
import SignedLeaf079
import SignedLeaf080
import SignedLeaf087
import SignedLeaf090
import SignedLeaf095
import SignedLeaf111
import SignedLeaf112
import SignedLeaf123
import SignedLeaf130
import SignedLeaf133

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0134 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000, 0x0), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0134 : List (List Sig) := []
private def bC0134 : List (List Sig) := [sC0135, sC0136, sC0137, sC0138, sC0139, sC0140, sC0141, sC0142, sC0143, sC0144, sC0145, sC0146, sC0147, sC0148, sC0149, sC0150, sC0151, sC0152, sC0153, sC0154, sC0155, sC0156]
theorem qC0134 : Impossible 8 1 sC0134 := by
  apply cut (us := aC0134) (bs := bC0134) (by decide +kernel)
  · decide +kernel
  · simp [aC0134]
  · intro x hx
    simp only [bC0134, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0135
    · exact qC0136
    · exact qC0137
    · exact qC0138
    · exact qC0139
    · exact qC0140
    · exact qC0141
    · exact qC0142
    · exact qC0143
    · exact qC0144
    · exact qC0145
    · exact qC0146
    · exact qC0147
    · exact qC0148
    · exact qC0149
    · exact qC0150
    · exact qC0151
    · exact qC0152
    · exact qC0153
    · exact qC0154
    · exact qC0155
    · exact qC0156

end Lower24992
