import Case24992
import SignedLeaf008
import SignedLeaf009
import SignedLeaf010
import SignedLeaf077
import SignedLeaf091
import SignedLeaf094
import SignedLeaf099
import SignedLeaf101
import SignedLeaf107
import SignedLeaf109
import SignedLeaf113
import SignedLeaf114
import SignedLeaf116
import SignedLeaf117
import SignedLeaf120
import SignedLeaf122
import SignedLeaf123
import SignedLeaf126
import SignedLeaf131

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0697 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3fffffffffffffffffffffffffff, 0x16ec5bb16ec5bb16ec5bb16ec5bb)]
private def aC0697 : List (List Sig) := []
private def bC0697 : List (List Sig) := [sC0698, sC0699, sC0700, sC0701, sC0702, sC0703, sC0704, sC0705, sC0706, sC0707, sC0708, sC0709, sC0710, sC0711, sC0712, sC0713, sC0714, sC0715, sC0716, sC0717, sC0718, sC0719, sC0720, sC0721, sC0722, sC0723, sC0724, sC0725, sC0726, sC0727, sC0728, sC0729, sC0730, sC0731, sC0732, sC0733, sC0734, sC0735, sC0736, sC0737, sC0738, sC0739, sC0740, sC0741]
theorem qC0697 : Impossible 8 1 sC0697 := by
  apply cut (us := aC0697) (bs := bC0697) (by decide +kernel)
  · decide +kernel
  · simp [aC0697]
  · intro x hx
    simp only [bC0697, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0698
    · exact qC0699
    · exact qC0700
    · exact qC0701
    · exact qC0702
    · exact qC0703
    · exact qC0704
    · exact qC0705
    · exact qC0706
    · exact qC0707
    · exact qC0708
    · exact qC0709
    · exact qC0710
    · exact qC0711
    · exact qC0712
    · exact qC0713
    · exact qC0714
    · exact qC0715
    · exact qC0716
    · exact qC0717
    · exact qC0718
    · exact qC0719
    · exact qC0720
    · exact qC0721
    · exact qC0722
    · exact qC0723
    · exact qC0724
    · exact qC0725
    · exact qC0726
    · exact qC0727
    · exact qC0728
    · exact qC0729
    · exact qC0730
    · exact qC0731
    · exact qC0732
    · exact qC0733
    · exact qC0734
    · exact qC0735
    · exact qC0736
    · exact qC0737
    · exact qC0738
    · exact qC0739
    · exact qC0740
    · exact qC0741

end Lower24992
