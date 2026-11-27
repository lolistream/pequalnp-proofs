import Case24992
import SignedLeaf058
import SignedLeaf063
import SignedLeaf079
import SignedLeaf082
import SignedLeaf085
import SignedLeaf091
import SignedLeaf100
import SignedLeaf103
import SignedLeaf107
import SignedLeaf108
import SignedLeaf113
import SignedLeaf114
import SignedLeaf122
import SignedLeaf123
import SignedLeaf125
import SignedLeaf129
import SignedLeaf131
import SignedLeaf134

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0595 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffc0000000000ffffffffffffff, 0x1fc07f01fc07f01fc07f01fc07f)]
private def aC0595 : List (List Sig) := []
private def bC0595 : List (List Sig) := [sC0596, sC0597, sC0598, sC0599, sC0600, sC0601, sC0602, sC0603, sC0604, sC0605, sC0123, sC0606, sC0169, sC0170, sC0607, sC0239, sC0290, sC0608, sC0321, sC0609, sC0351, sC0373, sC0610, sC0611, sC0612, sC0613, sC0614, sC0615, sC0616, sC0375, sC0376, sC0617, sC0618, sC0489, sC0517, sC0544, sC0571]
theorem qC0595 : Impossible 8 1 sC0595 := by
  apply cut (us := aC0595) (bs := bC0595) (by decide +kernel)
  · decide +kernel
  · simp [aC0595]
  · intro x hx
    simp only [bC0595, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0596
    · exact qC0597
    · exact qC0598
    · exact qC0599
    · exact qC0600
    · exact qC0601
    · exact qC0602
    · exact qC0603
    · exact qC0604
    · exact qC0605
    · exact qC0123
    · exact qC0606
    · exact qC0169
    · exact qC0170
    · exact qC0607
    · exact qC0239
    · exact qC0290
    · exact qC0608
    · exact qC0321
    · exact qC0609
    · exact qC0351
    · exact qC0373
    · exact qC0610
    · exact qC0611
    · exact qC0612
    · exact qC0613
    · exact qC0614
    · exact qC0615
    · exact qC0616
    · exact qC0375
    · exact qC0376
    · exact qC0617
    · exact qC0618
    · exact qC0489
    · exact qC0517
    · exact qC0544
    · exact qC0571

end Lower24992
