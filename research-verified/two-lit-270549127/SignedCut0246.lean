import Case24992
import SignedCut0071
import SignedLeaf040
import SignedLeaf054
import SignedLeaf056
import SignedLeaf057
import SignedLeaf094
import SignedLeaf099
import SignedLeaf100
import SignedLeaf105
import SignedLeaf115
import SignedLeaf117
import SignedLeaf119
import SignedLeaf121
import SignedLeaf133

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0246 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0x3fffffffffffffc000, 0xfe03f80fe03f80fe03f80fe03f8), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0246 : List (List Sig) := []
private def bC0246 : List (List Sig) := [sC0037, sC0055, sC0071, sC0247, sC0248, sC0249, sC0250, sC0251, sC0252, sC0253, sC0254, sC0255, sC0256, sC0197, sC0257, sC0258, sC0259, sC0260, sC0233, sC0261, sC0262, sC0263, sC0202, sC0264, sC0265, sC0266]
theorem qC0246 : Impossible 8 1 sC0246 := by
  apply cut (us := aC0246) (bs := bC0246) (by decide +kernel)
  · decide +kernel
  · simp [aC0246]
  · intro x hx
    simp only [bC0246, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0037
    · exact qC0055
    · exact qC0071
    · exact qC0247
    · exact qC0248
    · exact qC0249
    · exact qC0250
    · exact qC0251
    · exact qC0252
    · exact qC0253
    · exact qC0254
    · exact qC0255
    · exact qC0256
    · exact qC0197
    · exact qC0257
    · exact qC0258
    · exact qC0259
    · exact qC0260
    · exact qC0233
    · exact qC0261
    · exact qC0262
    · exact qC0263
    · exact qC0202
    · exact qC0264
    · exact qC0265
    · exact qC0266

end Lower24992
