import Case24992
import SignedLeaf021
import SignedLeaf027
import SignedLeaf078
import SignedLeaf080
import SignedLeaf082
import SignedLeaf085
import SignedLeaf091
import SignedLeaf092
import SignedLeaf103
import SignedLeaf106
import SignedLeaf107
import SignedLeaf108
import SignedLeaf111
import SignedLeaf115
import SignedLeaf116
import SignedLeaf119
import SignedLeaf121

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0299 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0299 : List (List Sig) := []
private def bC0299 : List (List Sig) := [sC0300, sC0301, sC0302, sC0303, sC0304, sC0305, sC0306, sC0307, sC0113, sC0308, sC0309, sC0310, sC0311, sC0199, sC0230, sC0281, sC0312, sC0313, sC0314, sC0315, sC0316, sC0317, sC0318, sC0319, sC0320, sC0321, sC0209, sC0241, sC0291, sC0322, sC0323, sC0324, sC0325, sC0326]
theorem qC0299 : Impossible 8 1 sC0299 := by
  apply cut (us := aC0299) (bs := bC0299) (by decide +kernel)
  · decide +kernel
  · simp [aC0299]
  · intro x hx
    simp only [bC0299, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0300
    · exact qC0301
    · exact qC0302
    · exact qC0303
    · exact qC0304
    · exact qC0305
    · exact qC0306
    · exact qC0307
    · exact qC0113
    · exact qC0308
    · exact qC0309
    · exact qC0310
    · exact qC0311
    · exact qC0199
    · exact qC0230
    · exact qC0281
    · exact qC0312
    · exact qC0313
    · exact qC0314
    · exact qC0315
    · exact qC0316
    · exact qC0317
    · exact qC0318
    · exact qC0319
    · exact qC0320
    · exact qC0321
    · exact qC0209
    · exact qC0241
    · exact qC0291
    · exact qC0322
    · exact qC0323
    · exact qC0324
    · exact qC0325
    · exact qC0326

end Lower24992
