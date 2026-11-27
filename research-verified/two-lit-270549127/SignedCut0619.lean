import Case24992
import SignedCut0620
import SignedCut0660
import SignedCut0697
import SignedCut0742
import SignedCut0782
import SignedCut0822
import SignedCut0862
import SignedCut0907
import SignedCut0939
import SignedCut0951
import SignedCut0970
import SignedCut0986
import SignedCut1001
import SignedCut1018
import SignedCut1033
import SignedCut1046
import SignedCut1058
import SignedCut1068
import SignedLeaf005
import SignedLeaf006
import SignedLeaf031
import SignedLeaf038
import SignedLeaf039
import SignedLeaf041
import SignedLeaf047
import SignedLeaf051
import SignedLeaf052
import SignedLeaf055
import SignedLeaf073
import SignedLeaf074
import SignedLeaf076
import SignedLeaf077
import SignedLeaf089
import SignedLeaf094
import SignedLeaf104
import SignedLeaf105
import SignedLeaf107

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0619 : List Sig := [(0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x0, 0x2913a44e913a44e913a44e913a44)]
private def aC0619 : List (List Sig) := [sC0620, sC0660, sC0693, sC0694, sC0695, sC0696, sC0697, sC0742, sC0782, sC0822, sC0862, sC0902]
private def bC0619 : List (List Sig) := [sC0903, sC0904, sC0905, sC0906, sC0907, sC0919, sC0920, sC0921, sC0922, sC0923, sC0924, sC0925, sC0926, sC0927, sC0928, sC0929, sC0930, sC0931, sC0932, sC0933, sC0934, sC0935, sC0936, sC0937, sC0938, sC0939, sC0947, sC0948, sC0949, sC0950, sC0951, sC0970, sC0986, sC1001, sC1018, sC1033, sC1046, sC1058, sC1068]
theorem qC0619 : Impossible 9 2 sC0619 := by
  apply cut (us := aC0619) (bs := bC0619) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC0619, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0620
    · exact qC0660
    · exact qC0693
    · exact qC0694
    · exact qC0695
    · exact qC0696
    · exact qC0697
    · exact qC0742
    · exact qC0782
    · exact qC0822
    · exact qC0862
    · exact qC0902
  · intro x hx
    simp only [bC0619, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0903
    · exact qC0904
    · exact qC0905
    · exact qC0906
    · exact qC0907
    · exact qC0919
    · exact qC0920
    · exact qC0921
    · exact qC0922
    · exact qC0923
    · exact qC0924
    · exact qC0925
    · exact qC0926
    · exact qC0927
    · exact qC0928
    · exact qC0929
    · exact qC0930
    · exact qC0931
    · exact qC0932
    · exact qC0933
    · exact qC0934
    · exact qC0935
    · exact qC0936
    · exact qC0937
    · exact qC0938
    · exact qC0939
    · exact qC0947
    · exact qC0948
    · exact qC0949
    · exact qC0950
    · exact qC0951
    · exact qC0970
    · exact qC0986
    · exact qC1001
    · exact qC1018
    · exact qC1033
    · exact qC1046
    · exact qC1058
    · exact qC1068

end Lower24992
