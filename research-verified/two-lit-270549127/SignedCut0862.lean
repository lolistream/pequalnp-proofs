import Case24992
import SignedLeaf060
import SignedLeaf069
import SignedLeaf071
import SignedLeaf080
import SignedLeaf083
import SignedLeaf094
import SignedLeaf100
import SignedLeaf101
import SignedLeaf103
import SignedLeaf110
import SignedLeaf112
import SignedLeaf117
import SignedLeaf120
import SignedLeaf123
import SignedLeaf128
import SignedLeaf132
import SignedLeaf133

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0862 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3fffffffffffff0003fff0003fff, 0x3e1ff87fe1ff87fe1ff87fe1ff87)]
private def aC0862 : List (List Sig) := []
private def bC0862 : List (List Sig) := [sC0863, sC0864, sC0865, sC0866, sC0867, sC0868, sC0869, sC0870, sC0871, sC0872, sC0873, sC0874, sC0875, sC0876, sC0877, sC0878, sC0879, sC0880, sC0881, sC0882, sC0883, sC0884, sC0885, sC0886, sC0887, sC0888, sC0889, sC0890, sC0891, sC0892, sC0893, sC0894, sC0895, sC0896, sC0897, sC0898, sC0899, sC0900, sC0901]
theorem qC0862 : Impossible 8 1 sC0862 := by
  apply cut (us := aC0862) (bs := bC0862) (by decide +kernel)
  · decide +kernel
  · simp [aC0862]
  · intro x hx
    simp only [bC0862, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0863
    · exact qC0864
    · exact qC0865
    · exact qC0866
    · exact qC0867
    · exact qC0868
    · exact qC0869
    · exact qC0870
    · exact qC0871
    · exact qC0872
    · exact qC0873
    · exact qC0874
    · exact qC0875
    · exact qC0876
    · exact qC0877
    · exact qC0878
    · exact qC0879
    · exact qC0880
    · exact qC0881
    · exact qC0882
    · exact qC0883
    · exact qC0884
    · exact qC0885
    · exact qC0886
    · exact qC0887
    · exact qC0888
    · exact qC0889
    · exact qC0890
    · exact qC0891
    · exact qC0892
    · exact qC0893
    · exact qC0894
    · exact qC0895
    · exact qC0896
    · exact qC0897
    · exact qC0898
    · exact qC0899
    · exact qC0900
    · exact qC0901

end Lower24992
