import Case24992
import SignedLeaf013
import SignedLeaf058
import SignedLeaf066
import SignedLeaf079
import SignedLeaf080
import SignedLeaf090
import SignedLeaf101
import SignedLeaf102
import SignedLeaf111
import SignedLeaf112
import SignedLeaf123
import SignedLeaf130
import SignedLeaf133

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0157 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0x3fff0000000, 0x0), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0157 : List (List Sig) := []
private def bC0157 : List (List Sig) := [sC0158, sC0159, sC0160, sC0161, sC0162, sC0163, sC0164, sC0165, sC0166, sC0167, sC0168, sC0169, sC0170, sC0171, sC0172, sC0173, sC0174, sC0175, sC0176, sC0177, sC0178, sC0179]
theorem qC0157 : Impossible 8 1 sC0157 := by
  apply cut (us := aC0157) (bs := bC0157) (by decide +kernel)
  · decide +kernel
  · simp [aC0157]
  · intro x hx
    simp only [bC0157, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0158
    · exact qC0159
    · exact qC0160
    · exact qC0161
    · exact qC0162
    · exact qC0163
    · exact qC0164
    · exact qC0165
    · exact qC0166
    · exact qC0167
    · exact qC0168
    · exact qC0169
    · exact qC0170
    · exact qC0171
    · exact qC0172
    · exact qC0173
    · exact qC0174
    · exact qC0175
    · exact qC0176
    · exact qC0177
    · exact qC0178
    · exact qC0179

end Lower24992
