import Case24992
import SignedLeaf005
import SignedLeaf006
import SignedLeaf007
import SignedLeaf008
import SignedLeaf012
import SignedLeaf032
import SignedLeaf033
import SignedLeaf035
import SignedLeaf052
import SignedLeaf053
import SignedLeaf055
import SignedLeaf056
import SignedLeaf063
import SignedLeaf075
import SignedLeaf088
import SignedLeaf094
import SignedLeaf096
import SignedLeaf100
import SignedLeaf102
import SignedLeaf104
import SignedLeaf106
import SignedLeaf108
import SignedLeaf111
import SignedLeaf112
import SignedLeaf113
import SignedLeaf115
import SignedLeaf118
import SignedLeaf124

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0180 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0xfffc000fffc000, 0x29f3a7ce9f3a7ce9f3a7ce9f3a7c), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0180 : List (List Sig) := []
private def bC0180 : List (List Sig) := [sC0054, sC0181, sC0182, sC0183, sC0184, sC0185, sC0186, sC0187, sC0146, sC0188, sC0189, sC0190, sC0191, sC0192, sC0193, sC0194, sC0195, sC0196, sC0197, sC0198, sC0199, sC0200, sC0201, sC0202, sC0203, sC0204, sC0205, sC0206, sC0207, sC0208, sC0209, sC0210, sC0211, sC0212, sC0213]
theorem qC0180 : Impossible 8 1 sC0180 := by
  apply cut (us := aC0180) (bs := bC0180) (by decide +kernel)
  · decide +kernel
  · simp [aC0180]
  · intro x hx
    simp only [bC0180, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0054
    · exact qC0181
    · exact qC0182
    · exact qC0183
    · exact qC0184
    · exact qC0185
    · exact qC0186
    · exact qC0187
    · exact qC0146
    · exact qC0188
    · exact qC0189
    · exact qC0190
    · exact qC0191
    · exact qC0192
    · exact qC0193
    · exact qC0194
    · exact qC0195
    · exact qC0196
    · exact qC0197
    · exact qC0198
    · exact qC0199
    · exact qC0200
    · exact qC0201
    · exact qC0202
    · exact qC0203
    · exact qC0204
    · exact qC0205
    · exact qC0206
    · exact qC0207
    · exact qC0208
    · exact qC0209
    · exact qC0210
    · exact qC0211
    · exact qC0212
    · exact qC0213

end Lower24992
