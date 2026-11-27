import Case24992
import SignedLeaf056
import SignedLeaf078
import SignedLeaf084
import SignedLeaf089
import SignedLeaf094
import SignedLeaf095
import SignedLeaf099
import SignedLeaf100
import SignedLeaf101
import SignedLeaf102
import SignedLeaf105
import SignedLeaf109
import SignedLeaf114
import SignedLeaf118
import SignedLeaf129
import SignedLeaf130

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0986 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc0000003fff0003ffffffffff, 0xe3c38f0e3c38f0e3c38f0e3c38f)]
private def aC0986 : List (List Sig) := [sC0987, sC0988, sC0989, sC0990, sC0991, sC0992, sC0725, sC0776, sC0816, sC0993, sC0897, sC0994]
private def bC0986 : List (List Sig) := [sC0912, sC0959, sC0979, sC0995, sC0996, sC0997, sC0998, sC0999, sC1000]
theorem qC0986 : Impossible 8 2 sC0986 := by
  apply cut (us := aC0986) (bs := bC0986) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC0986, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0987
    · exact qC0988
    · exact qC0989
    · exact qC0990
    · exact qC0991
    · exact qC0992
    · exact qC0725
    · exact qC0776
    · exact qC0816
    · exact qC0993
    · exact qC0897
    · exact qC0994
  · intro x hx
    simp only [bC0986, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0912
    · exact qC0959
    · exact qC0979
    · exact qC0995
    · exact qC0996
    · exact qC0997
    · exact qC0998
    · exact qC0999
    · exact qC1000

end Lower24992
