import Case24992
import SignedCut0057
import SignedLeaf005
import SignedLeaf035
import SignedLeaf040
import SignedLeaf044
import SignedLeaf050
import SignedLeaf053
import SignedLeaf060
import SignedLeaf063
import SignedLeaf073
import SignedLeaf075
import SignedLeaf076
import SignedLeaf098
import SignedLeaf101
import SignedLeaf104
import SignedLeaf105
import SignedLeaf106
import SignedLeaf110
import SignedLeaf113
import SignedLeaf121
import SignedLeaf124
import SignedLeaf129
import SignedLeaf133

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0412 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc0000000000ffffffffffffff, 0x1fc07f01fc07f01fc07f01fc07f)]
private def aC0412 : List (List Sig) := []
private def bC0412 : List (List Sig) := [sC0413, sC0009, sC0057, sC0414, sC0415, sC0416, sC0417, sC0418, sC0419, sC0420, sC0421, sC0422, sC0111, sC0423, sC0424, sC0190, sC0224, sC0252, sC0278, sC0425, sC0426, sC0310, sC0427, sC0428, sC0337, sC0429, sC0430, sC0431, sC0432, sC0201, sC0260, sC0433, sC0434, sC0435, sC0206, sC0436, sC0437]
theorem qC0412 : Impossible 8 1 sC0412 := by
  apply cut (us := aC0412) (bs := bC0412) (by decide +kernel)
  · decide +kernel
  · simp [aC0412]
  · intro x hx
    simp only [bC0412, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0413
    · exact qC0009
    · exact qC0057
    · exact qC0414
    · exact qC0415
    · exact qC0416
    · exact qC0417
    · exact qC0418
    · exact qC0419
    · exact qC0420
    · exact qC0421
    · exact qC0422
    · exact qC0111
    · exact qC0423
    · exact qC0424
    · exact qC0190
    · exact qC0224
    · exact qC0252
    · exact qC0278
    · exact qC0425
    · exact qC0426
    · exact qC0310
    · exact qC0427
    · exact qC0428
    · exact qC0337
    · exact qC0429
    · exact qC0430
    · exact qC0431
    · exact qC0432
    · exact qC0201
    · exact qC0260
    · exact qC0433
    · exact qC0434
    · exact qC0435
    · exact qC0206
    · exact qC0436
    · exact qC0437

end Lower24992
