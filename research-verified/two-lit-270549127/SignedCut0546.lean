import Case24992
import SignedLeaf058
import SignedLeaf062
import SignedLeaf063
import SignedLeaf079
import SignedLeaf082
import SignedLeaf083
import SignedLeaf085
import SignedLeaf088
import SignedLeaf090
import SignedLeaf103
import SignedLeaf106
import SignedLeaf107
import SignedLeaf108
import SignedLeaf113
import SignedLeaf114
import SignedLeaf121
import SignedLeaf122
import SignedLeaf123
import SignedLeaf124
import SignedLeaf129
import SignedLeaf130
import SignedLeaf131
import SignedLeaf134

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0546 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffc0000003fff0003ffffffffff, 0xe3c38f0e3c38f0e3c38f0e3c38f)]
private def aC0546 : List (List Sig) := []
private def bC0546 : List (List Sig) := [sC0547, sC0548, sC0549, sC0550, sC0551, sC0552, sC0553, sC0554, sC0555, sC0556, sC0120, sC0557, sC0144, sC0145, sC0558, sC0196, sC0288, sC0559, sC0319, sC0560, sC0349, sC0368, sC0561, sC0562, sC0563, sC0564, sC0565, sC0566, sC0567, sC0370, sC0371, sC0568, sC0569, sC0487, sC0515, sC0570, sC0571]
theorem qC0546 : Impossible 8 1 sC0546 := by
  apply cut (us := aC0546) (bs := bC0546) (by decide +kernel)
  · decide +kernel
  · simp [aC0546]
  · intro x hx
    simp only [bC0546, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0547
    · exact qC0548
    · exact qC0549
    · exact qC0550
    · exact qC0551
    · exact qC0552
    · exact qC0553
    · exact qC0554
    · exact qC0555
    · exact qC0556
    · exact qC0120
    · exact qC0557
    · exact qC0144
    · exact qC0145
    · exact qC0558
    · exact qC0196
    · exact qC0288
    · exact qC0559
    · exact qC0319
    · exact qC0560
    · exact qC0349
    · exact qC0368
    · exact qC0561
    · exact qC0562
    · exact qC0563
    · exact qC0564
    · exact qC0565
    · exact qC0566
    · exact qC0567
    · exact qC0370
    · exact qC0371
    · exact qC0568
    · exact qC0569
    · exact qC0487
    · exact qC0515
    · exact qC0570
    · exact qC0571

end Lower24992
