import Case24992
import SignedLeaf006
import SignedLeaf067
import SignedLeaf075
import SignedLeaf079
import SignedLeaf083
import SignedLeaf085
import SignedLeaf090
import SignedLeaf094
import SignedLeaf100
import SignedLeaf101
import SignedLeaf103
import SignedLeaf107
import SignedLeaf108
import SignedLeaf109
import SignedLeaf114
import SignedLeaf115
import SignedLeaf116
import SignedLeaf119
import SignedLeaf129

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0352 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffc00000000000003ffffffffff, 0x291fa47e91fa47e91fa47e91fa47)]
private def aC0352 : List (List Sig) := []
private def bC0352 : List (List Sig) := [sC0353, sC0354, sC0355, sC0356, sC0357, sC0358, sC0135, sC0359, sC0158, sC0360, sC0200, sC0231, sC0282, sC0312, sC0361, sC0362, sC0363, sC0364, sC0365, sC0366, sC0367, sC0368, sC0369, sC0370, sC0371, sC0372, sC0373, sC0374, sC0375, sC0376, sC0210, sC0242, sC0292, sC0322, sC0377, sC0378]
theorem qC0352 : Impossible 8 1 sC0352 := by
  apply cut (us := aC0352) (bs := bC0352) (by decide +kernel)
  · decide +kernel
  · simp [aC0352]
  · intro x hx
    simp only [bC0352, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0353
    · exact qC0354
    · exact qC0355
    · exact qC0356
    · exact qC0357
    · exact qC0358
    · exact qC0135
    · exact qC0359
    · exact qC0158
    · exact qC0360
    · exact qC0200
    · exact qC0231
    · exact qC0282
    · exact qC0312
    · exact qC0361
    · exact qC0362
    · exact qC0363
    · exact qC0364
    · exact qC0365
    · exact qC0366
    · exact qC0367
    · exact qC0368
    · exact qC0369
    · exact qC0370
    · exact qC0371
    · exact qC0372
    · exact qC0373
    · exact qC0374
    · exact qC0375
    · exact qC0376
    · exact qC0210
    · exact qC0242
    · exact qC0292
    · exact qC0322
    · exact qC0377
    · exact qC0378

end Lower24992
