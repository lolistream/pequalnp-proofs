import Case24992
import SignedLeaf059
import SignedLeaf060
import SignedLeaf065
import SignedLeaf071
import SignedLeaf079
import SignedLeaf083
import SignedLeaf094
import SignedLeaf100
import SignedLeaf101
import SignedLeaf103
import SignedLeaf110
import SignedLeaf112
import SignedLeaf116
import SignedLeaf117
import SignedLeaf120
import SignedLeaf123
import SignedLeaf127
import SignedLeaf128
import SignedLeaf132

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0822 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3fffffffffc000fffc000fffffff, 0x31dfc77f1dfc77f1dfc77f1dfc77)]
private def aC0822 : List (List Sig) := []
private def bC0822 : List (List Sig) := [sC0823, sC0824, sC0825, sC0826, sC0827, sC0828, sC0829, sC0830, sC0831, sC0832, sC0833, sC0834, sC0835, sC0836, sC0837, sC0838, sC0839, sC0840, sC0841, sC0842, sC0843, sC0844, sC0845, sC0846, sC0847, sC0848, sC0849, sC0850, sC0851, sC0852, sC0853, sC0854, sC0855, sC0856, sC0857, sC0858, sC0859, sC0860, sC0861]
theorem qC0822 : Impossible 8 1 sC0822 := by
  apply cut (us := aC0822) (bs := bC0822) (by decide +kernel)
  · decide +kernel
  · simp [aC0822]
  · intro x hx
    simp only [bC0822, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0823
    · exact qC0824
    · exact qC0825
    · exact qC0826
    · exact qC0827
    · exact qC0828
    · exact qC0829
    · exact qC0830
    · exact qC0831
    · exact qC0832
    · exact qC0833
    · exact qC0834
    · exact qC0835
    · exact qC0836
    · exact qC0837
    · exact qC0838
    · exact qC0839
    · exact qC0840
    · exact qC0841
    · exact qC0842
    · exact qC0843
    · exact qC0844
    · exact qC0845
    · exact qC0846
    · exact qC0847
    · exact qC0848
    · exact qC0849
    · exact qC0850
    · exact qC0851
    · exact qC0852
    · exact qC0853
    · exact qC0854
    · exact qC0855
    · exact qC0856
    · exact qC0857
    · exact qC0858
    · exact qC0859
    · exact qC0860
    · exact qC0861

end Lower24992
