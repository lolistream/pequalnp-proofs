import Case24992
import SignedLeaf075
import SignedLeaf082
import SignedLeaf083
import SignedLeaf104
import SignedLeaf110
import SignedLeaf112
import SignedLeaf119
import SignedLeaf120
import SignedLeaf125
import SignedLeaf126
import SignedLeaf131
import SignedLeaf134

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0620 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3fffffffffffffc0000000000, 0x3fe3ff8ffe3ff8ffe3ff8ffe3ff8)]
private def aC0620 : List (List Sig) := []
private def bC0620 : List (List Sig) := [sC0621, sC0622, sC0623, sC0624, sC0625, sC0626, sC0627, sC0628, sC0629, sC0630, sC0631, sC0632, sC0633, sC0634, sC0635, sC0636, sC0637, sC0638, sC0639, sC0640, sC0641, sC0642, sC0643, sC0644, sC0645, sC0646, sC0647, sC0648, sC0649, sC0650, sC0651, sC0652, sC0653, sC0654, sC0655, sC0656, sC0657, sC0658, sC0659]
theorem qC0620 : Impossible 8 1 sC0620 := by
  apply cut (us := aC0620) (bs := bC0620) (by decide +kernel)
  · decide +kernel
  · simp [aC0620]
  · intro x hx
    simp only [bC0620, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0621
    · exact qC0622
    · exact qC0623
    · exact qC0624
    · exact qC0625
    · exact qC0626
    · exact qC0627
    · exact qC0628
    · exact qC0629
    · exact qC0630
    · exact qC0631
    · exact qC0632
    · exact qC0633
    · exact qC0634
    · exact qC0635
    · exact qC0636
    · exact qC0637
    · exact qC0638
    · exact qC0639
    · exact qC0640
    · exact qC0641
    · exact qC0642
    · exact qC0643
    · exact qC0644
    · exact qC0645
    · exact qC0646
    · exact qC0647
    · exact qC0648
    · exact qC0649
    · exact qC0650
    · exact qC0651
    · exact qC0652
    · exact qC0653
    · exact qC0654
    · exact qC0655
    · exact qC0656
    · exact qC0657
    · exact qC0658
    · exact qC0659

end Lower24992
