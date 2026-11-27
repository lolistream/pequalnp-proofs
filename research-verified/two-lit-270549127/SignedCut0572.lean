import Case24992
import SignedLeaf010
import SignedLeaf037
import SignedLeaf039
import SignedLeaf047
import SignedLeaf048
import SignedLeaf050
import SignedLeaf053
import SignedLeaf055
import SignedLeaf059
import SignedLeaf070
import SignedLeaf072
import SignedLeaf078
import SignedLeaf079
import SignedLeaf082
import SignedLeaf083
import SignedLeaf086
import SignedLeaf088
import SignedLeaf098
import SignedLeaf101
import SignedLeaf102
import SignedLeaf103
import SignedLeaf108
import SignedLeaf110
import SignedLeaf111
import SignedLeaf112
import SignedLeaf116
import SignedLeaf124
import SignedLeaf125

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0572 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x29f3a7ce9f3a7ce9f3a7ce9f3a7c), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0572 : List (List Sig) := []
private def bC0572 : List (List Sig) := [sC0573, sC0574, sC0575, sC0576, sC0577, sC0578, sC0579, sC0580, sC0581, sC0122, sC0582, sC0583, sC0584, sC0167, sC0238, sC0585, sC0289, sC0586, sC0587, sC0320, sC0588, sC0589, sC0350, sC0372, sC0590, sC0591, sC0592, sC0593, sC0408, sC0594, sC0463, sC0488, sC0516, sC0543, sC0570, sC0375, sC0245, sC0296, sC0326, sC0492, sC0519, sC0545]
theorem qC0572 : Impossible 8 1 sC0572 := by
  apply cut (us := aC0572) (bs := bC0572) (by decide +kernel)
  · decide +kernel
  · simp [aC0572]
  · intro x hx
    simp only [bC0572, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0573
    · exact qC0574
    · exact qC0575
    · exact qC0576
    · exact qC0577
    · exact qC0578
    · exact qC0579
    · exact qC0580
    · exact qC0581
    · exact qC0122
    · exact qC0582
    · exact qC0583
    · exact qC0584
    · exact qC0167
    · exact qC0238
    · exact qC0585
    · exact qC0289
    · exact qC0586
    · exact qC0587
    · exact qC0320
    · exact qC0588
    · exact qC0589
    · exact qC0350
    · exact qC0372
    · exact qC0590
    · exact qC0591
    · exact qC0592
    · exact qC0593
    · exact qC0408
    · exact qC0594
    · exact qC0463
    · exact qC0488
    · exact qC0516
    · exact qC0543
    · exact qC0570
    · exact qC0375
    · exact qC0245
    · exact qC0296
    · exact qC0326
    · exact qC0492
    · exact qC0519
    · exact qC0545

end Lower24992
