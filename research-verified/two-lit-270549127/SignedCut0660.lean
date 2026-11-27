import Case24992
import SignedLeaf022
import SignedLeaf023
import SignedLeaf059
import SignedLeaf062
import SignedLeaf071
import SignedLeaf076
import SignedLeaf101
import SignedLeaf113
import SignedLeaf114
import SignedLeaf117
import SignedLeaf120
import SignedLeaf122
import SignedLeaf126
import SignedLeaf134

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0660 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3fffffffffffffc0000000000, 0x3fe3ff8ffe3ff8ffe3ff8ffe3ff8), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0660 : List (List Sig) := []
private def bC0660 : List (List Sig) := [sC0661, sC0662, sC0663, sC0664, sC0665, sC0666, sC0667, sC0668, sC0669, sC0670, sC0671, sC0672, sC0673, sC0674, sC0675, sC0676, sC0677, sC0678, sC0679, sC0680, sC0681, sC0682, sC0683, sC0684, sC0685, sC0686, sC0687, sC0688, sC0689, sC0690, sC0691, sC0692]
theorem qC0660 : Impossible 8 1 sC0660 := by
  apply cut (us := aC0660) (bs := bC0660) (by decide +kernel)
  · decide +kernel
  · simp [aC0660]
  · intro x hx
    simp only [bC0660, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0661
    · exact qC0662
    · exact qC0663
    · exact qC0664
    · exact qC0665
    · exact qC0666
    · exact qC0667
    · exact qC0668
    · exact qC0669
    · exact qC0670
    · exact qC0671
    · exact qC0672
    · exact qC0673
    · exact qC0674
    · exact qC0675
    · exact qC0676
    · exact qC0677
    · exact qC0678
    · exact qC0679
    · exact qC0680
    · exact qC0681
    · exact qC0682
    · exact qC0683
    · exact qC0684
    · exact qC0685
    · exact qC0686
    · exact qC0687
    · exact qC0688
    · exact qC0689
    · exact qC0690
    · exact qC0691
    · exact qC0692

end Lower24992
