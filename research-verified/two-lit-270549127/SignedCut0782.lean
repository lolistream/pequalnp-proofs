import Case24992
import SignedLeaf064
import SignedLeaf088
import SignedLeaf089
import SignedLeaf098
import SignedLeaf099
import SignedLeaf100
import SignedLeaf105
import SignedLeaf106
import SignedLeaf108
import SignedLeaf110
import SignedLeaf112
import SignedLeaf115
import SignedLeaf120
import SignedLeaf126
import SignedLeaf127
import SignedLeaf129
import SignedLeaf132
import SignedLeaf134

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0782 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffffff0003fffffffffffffffff, 0xdbb36ecdbb36ecdbb36ecdbb36e)]
private def aC0782 : List (List Sig) := []
private def bC0782 : List (List Sig) := [sC0783, sC0784, sC0785, sC0786, sC0787, sC0788, sC0789, sC0790, sC0791, sC0792, sC0793, sC0794, sC0795, sC0796, sC0797, sC0798, sC0799, sC0800, sC0801, sC0802, sC0803, sC0804, sC0805, sC0806, sC0807, sC0808, sC0809, sC0810, sC0811, sC0812, sC0813, sC0814, sC0815, sC0816, sC0817, sC0818, sC0819, sC0820, sC0821]
theorem qC0782 : Impossible 8 1 sC0782 := by
  apply cut (us := aC0782) (bs := bC0782) (by decide +kernel)
  · decide +kernel
  · simp [aC0782]
  · intro x hx
    simp only [bC0782, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0783
    · exact qC0784
    · exact qC0785
    · exact qC0786
    · exact qC0787
    · exact qC0788
    · exact qC0789
    · exact qC0790
    · exact qC0791
    · exact qC0792
    · exact qC0793
    · exact qC0794
    · exact qC0795
    · exact qC0796
    · exact qC0797
    · exact qC0798
    · exact qC0799
    · exact qC0800
    · exact qC0801
    · exact qC0802
    · exact qC0803
    · exact qC0804
    · exact qC0805
    · exact qC0806
    · exact qC0807
    · exact qC0808
    · exact qC0809
    · exact qC0810
    · exact qC0811
    · exact qC0812
    · exact qC0813
    · exact qC0814
    · exact qC0815
    · exact qC0816
    · exact qC0817
    · exact qC0818
    · exact qC0819
    · exact qC0820
    · exact qC0821

end Lower24992
