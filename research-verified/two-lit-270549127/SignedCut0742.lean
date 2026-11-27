import Case24992
import SignedLeaf049
import SignedLeaf088
import SignedLeaf089
import SignedLeaf098
import SignedLeaf099
import SignedLeaf100
import SignedLeaf105
import SignedLeaf106
import SignedLeaf108
import SignedLeaf109
import SignedLeaf112
import SignedLeaf114
import SignedLeaf120
import SignedLeaf126
import SignedLeaf129
import SignedLeaf131
import SignedLeaf132
import SignedLeaf134

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0742 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffc000fffffffffffffffffffff, 0x2b76addab76addab76addab76add)]
private def aC0742 : List (List Sig) := []
private def bC0742 : List (List Sig) := [sC0743, sC0744, sC0745, sC0746, sC0747, sC0748, sC0749, sC0750, sC0751, sC0752, sC0753, sC0754, sC0755, sC0756, sC0757, sC0758, sC0759, sC0760, sC0761, sC0762, sC0763, sC0764, sC0765, sC0766, sC0767, sC0768, sC0769, sC0770, sC0771, sC0772, sC0773, sC0774, sC0775, sC0776, sC0777, sC0778, sC0779, sC0780, sC0781]
theorem qC0742 : Impossible 8 1 sC0742 := by
  apply cut (us := aC0742) (bs := bC0742) (by decide +kernel)
  · decide +kernel
  · simp [aC0742]
  · intro x hx
    simp only [bC0742, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0743
    · exact qC0744
    · exact qC0745
    · exact qC0746
    · exact qC0747
    · exact qC0748
    · exact qC0749
    · exact qC0750
    · exact qC0751
    · exact qC0752
    · exact qC0753
    · exact qC0754
    · exact qC0755
    · exact qC0756
    · exact qC0757
    · exact qC0758
    · exact qC0759
    · exact qC0760
    · exact qC0761
    · exact qC0762
    · exact qC0763
    · exact qC0764
    · exact qC0765
    · exact qC0766
    · exact qC0767
    · exact qC0768
    · exact qC0769
    · exact qC0770
    · exact qC0771
    · exact qC0772
    · exact qC0773
    · exact qC0774
    · exact qC0775
    · exact qC0776
    · exact qC0777
    · exact qC0778
    · exact qC0779
    · exact qC0780
    · exact qC0781

end Lower24992
