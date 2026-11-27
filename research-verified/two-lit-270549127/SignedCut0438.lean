import Case24992
import SignedCut0039
import SignedLeaf036
import SignedLeaf040
import SignedLeaf045
import SignedLeaf050
import SignedLeaf053
import SignedLeaf064
import SignedLeaf076
import SignedLeaf078
import SignedLeaf086
import SignedLeaf099
import SignedLeaf101
import SignedLeaf104
import SignedLeaf105
import SignedLeaf106
import SignedLeaf110
import SignedLeaf113
import SignedLeaf114
import SignedLeaf121
import SignedLeaf124
import SignedLeaf129
import SignedLeaf133
import SignedLeaf134

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0438 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc0000003fff0003ffffffffff, 0xe3c38f0e3c38f0e3c38f0e3c38f)]
private def aC0438 : List (List Sig) := []
private def bC0438 : List (List Sig) := [sC0439, sC0010, sC0039, sC0440, sC0441, sC0442, sC0443, sC0444, sC0445, sC0446, sC0447, sC0448, sC0112, sC0449, sC0450, sC0192, sC0225, sC0253, sC0279, sC0451, sC0452, sC0311, sC0453, sC0454, sC0338, sC0455, sC0456, sC0457, sC0458, sC0232, sC0260, sC0459, sC0460, sC0237, sC0461, sC0462, sC0463]
theorem qC0438 : Impossible 8 1 sC0438 := by
  apply cut (us := aC0438) (bs := bC0438) (by decide +kernel)
  · decide +kernel
  · simp [aC0438]
  · intro x hx
    simp only [bC0438, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0439
    · exact qC0010
    · exact qC0039
    · exact qC0440
    · exact qC0441
    · exact qC0442
    · exact qC0443
    · exact qC0444
    · exact qC0445
    · exact qC0446
    · exact qC0447
    · exact qC0448
    · exact qC0112
    · exact qC0449
    · exact qC0450
    · exact qC0192
    · exact qC0225
    · exact qC0253
    · exact qC0279
    · exact qC0451
    · exact qC0452
    · exact qC0311
    · exact qC0453
    · exact qC0454
    · exact qC0338
    · exact qC0455
    · exact qC0456
    · exact qC0457
    · exact qC0458
    · exact qC0232
    · exact qC0260
    · exact qC0459
    · exact qC0460
    · exact qC0237
    · exact qC0461
    · exact qC0462
    · exact qC0463

end Lower24992
