import Case24992
import SignedLeaf011
import SignedLeaf014
import SignedLeaf015
import SignedLeaf035
import SignedLeaf036
import SignedLeaf049
import SignedLeaf056
import SignedLeaf057
import SignedLeaf078
import SignedLeaf082
import SignedLeaf086
import SignedLeaf094
import SignedLeaf100
import SignedLeaf103
import SignedLeaf104
import SignedLeaf106
import SignedLeaf109
import SignedLeaf115
import SignedLeaf116
import SignedLeaf129

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0383 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x291fa47e91fa47e91fa47e91fa47)]
private def aC0383 : List (List Sig) := []
private def bC0383 : List (List Sig) := [sC0384, sC0385, sC0008, sC0386, sC0387, sC0388, sC0389, sC0390, sC0391, sC0110, sC0392, sC0393, sC0394, sC0395, sC0189, sC0223, sC0251, sC0277, sC0396, sC0397, sC0309, sC0398, sC0399, sC0336, sC0400, sC0401, sC0402, sC0403, sC0201, sC0232, sC0404, sC0405, sC0406, sC0407, sC0408, sC0409, sC0293, sC0323, sC0410, sC0411]
theorem qC0383 : Impossible 8 1 sC0383 := by
  apply cut (us := aC0383) (bs := bC0383) (by decide +kernel)
  · decide +kernel
  · simp [aC0383]
  · intro x hx
    simp only [bC0383, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0384
    · exact qC0385
    · exact qC0008
    · exact qC0386
    · exact qC0387
    · exact qC0388
    · exact qC0389
    · exact qC0390
    · exact qC0391
    · exact qC0110
    · exact qC0392
    · exact qC0393
    · exact qC0394
    · exact qC0395
    · exact qC0189
    · exact qC0223
    · exact qC0251
    · exact qC0277
    · exact qC0396
    · exact qC0397
    · exact qC0309
    · exact qC0398
    · exact qC0399
    · exact qC0336
    · exact qC0400
    · exact qC0401
    · exact qC0402
    · exact qC0403
    · exact qC0201
    · exact qC0232
    · exact qC0404
    · exact qC0405
    · exact qC0406
    · exact qC0407
    · exact qC0408
    · exact qC0409
    · exact qC0293
    · exact qC0323
    · exact qC0410
    · exact qC0411

end Lower24992
