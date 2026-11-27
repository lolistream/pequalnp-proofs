import Case24992
import SignedLeaf016
import SignedLeaf037
import SignedLeaf041
import SignedLeaf048
import SignedLeaf060
import SignedLeaf070
import SignedLeaf078
import SignedLeaf080
import SignedLeaf085
import SignedLeaf100
import SignedLeaf108
import SignedLeaf109
import SignedLeaf110
import SignedLeaf111
import SignedLeaf114
import SignedLeaf119
import SignedLeaf120
import SignedLeaf121
import SignedLeaf129

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0329 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffffffc00000000000000000, 0x36cddb376cddb376cddb376cddb3), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0329 : List (List Sig) := []
private def bC0329 : List (List Sig) := [sC0330, sC0331, sC0332, sC0333, sC0334, sC0114, sC0116, sC0117, sC0335, sC0336, sC0337, sC0338, sC0281, sC0339, sC0340, sC0341, sC0315, sC0342, sC0343, sC0344, sC0285, sC0345, sC0346, sC0347, sC0348, sC0349, sC0350, sC0351]
theorem qC0329 : Impossible 8 1 sC0329 := by
  apply cut (us := aC0329) (bs := bC0329) (by decide +kernel)
  · decide +kernel
  · simp [aC0329]
  · intro x hx
    simp only [bC0329, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0330
    · exact qC0331
    · exact qC0332
    · exact qC0333
    · exact qC0334
    · exact qC0114
    · exact qC0116
    · exact qC0117
    · exact qC0335
    · exact qC0336
    · exact qC0337
    · exact qC0338
    · exact qC0281
    · exact qC0339
    · exact qC0340
    · exact qC0341
    · exact qC0315
    · exact qC0342
    · exact qC0343
    · exact qC0344
    · exact qC0285
    · exact qC0345
    · exact qC0346
    · exact qC0347
    · exact qC0348
    · exact qC0349
    · exact qC0350
    · exact qC0351

end Lower24992
