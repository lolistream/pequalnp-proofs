import Case24992
import SignedLeaf027
import SignedLeaf028
import SignedLeaf037
import SignedLeaf056
import SignedLeaf058
import SignedLeaf059
import SignedLeaf060
import SignedLeaf061
import SignedLeaf073
import SignedLeaf086
import SignedLeaf099
import SignedLeaf108
import SignedLeaf111
import SignedLeaf115
import SignedLeaf120
import SignedLeaf121

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0108 : List Sig := [(0x0, 0x1000400100040010004001000400), (0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0108 : List (List Sig) := []
private def bC0108 : List (List Sig) := [sC0109, sC0110, sC0111, sC0112, sC0113, sC0114, sC0115, sC0116, sC0117, sC0118, sC0119, sC0120, sC0121, sC0122, sC0123, sC0124, sC0125, sC0126, sC0127, sC0128, sC0129, sC0130, sC0131, sC0132]
theorem qC0108 : Impossible 8 1 sC0108 := by
  apply cut (us := aC0108) (bs := bC0108) (by decide +kernel)
  · decide +kernel
  · simp [aC0108]
  · intro x hx
    simp only [bC0108, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0109
    · exact qC0110
    · exact qC0111
    · exact qC0112
    · exact qC0113
    · exact qC0114
    · exact qC0115
    · exact qC0116
    · exact qC0117
    · exact qC0118
    · exact qC0119
    · exact qC0120
    · exact qC0121
    · exact qC0122
    · exact qC0123
    · exact qC0124
    · exact qC0125
    · exact qC0126
    · exact qC0127
    · exact qC0128
    · exact qC0129
    · exact qC0130
    · exact qC0131
    · exact qC0132

end Lower24992
