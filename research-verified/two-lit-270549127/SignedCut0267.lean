import Case24992
import SignedLeaf020
import SignedLeaf028
import SignedLeaf077
import SignedLeaf078
import SignedLeaf080
import SignedLeaf082
import SignedLeaf085
import SignedLeaf091
import SignedLeaf103
import SignedLeaf105
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

def sC0267 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0267 : List (List Sig) := []
private def bC0267 : List (List Sig) := [sC0268, sC0269, sC0270, sC0271, sC0272, sC0273, sC0115, sC0274, sC0275, sC0276, sC0277, sC0278, sC0279, sC0280, sC0198, sC0229, sC0281, sC0282, sC0283, sC0284, sC0285, sC0286, sC0287, sC0288, sC0289, sC0290, sC0208, sC0240, sC0291, sC0292, sC0293, sC0294, sC0295, sC0296]
theorem qC0267 : Impossible 8 1 sC0267 := by
  apply cut (us := aC0267) (bs := bC0267) (by decide +kernel)
  · decide +kernel
  · simp [aC0267]
  · intro x hx
    simp only [bC0267, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0268
    · exact qC0269
    · exact qC0270
    · exact qC0271
    · exact qC0272
    · exact qC0273
    · exact qC0115
    · exact qC0274
    · exact qC0275
    · exact qC0276
    · exact qC0277
    · exact qC0278
    · exact qC0279
    · exact qC0280
    · exact qC0198
    · exact qC0229
    · exact qC0281
    · exact qC0282
    · exact qC0283
    · exact qC0284
    · exact qC0285
    · exact qC0286
    · exact qC0287
    · exact qC0288
    · exact qC0289
    · exact qC0290
    · exact qC0208
    · exact qC0240
    · exact qC0291
    · exact qC0292
    · exact qC0293
    · exact qC0294
    · exact qC0295
    · exact qC0296

end Lower24992
