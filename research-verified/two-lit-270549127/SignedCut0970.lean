import Case24992
import SignedLeaf056
import SignedLeaf078
import SignedLeaf083
import SignedLeaf089
import SignedLeaf093
import SignedLeaf095
import SignedLeaf099
import SignedLeaf101
import SignedLeaf102
import SignedLeaf105
import SignedLeaf109
import SignedLeaf114
import SignedLeaf118
import SignedLeaf129

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0970 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc0000000000ffffffffffffff, 0x1fc07f01fc07f01fc07f01fc07f)]
private def aC0970 : List (List Sig) := [sC0971, sC0972, sC0973, sC0974, sC0975, sC0976, sC0724, sC0775, sC0815, sC0857, sC0977, sC0978]
private def bC0970 : List (List Sig) := [sC0913, sC0958, sC0979, sC0980, sC0981, sC0982, sC0983, sC0984, sC0985]
theorem qC0970 : Impossible 8 2 sC0970 := by
  apply cut (us := aC0970) (bs := bC0970) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC0970, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0971
    · exact qC0972
    · exact qC0973
    · exact qC0974
    · exact qC0975
    · exact qC0976
    · exact qC0724
    · exact qC0775
    · exact qC0815
    · exact qC0857
    · exact qC0977
    · exact qC0978
  · intro x hx
    simp only [bC0970, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0913
    · exact qC0958
    · exact qC0979
    · exact qC0980
    · exact qC0981
    · exact qC0982
    · exact qC0983
    · exact qC0984
    · exact qC0985

end Lower24992
