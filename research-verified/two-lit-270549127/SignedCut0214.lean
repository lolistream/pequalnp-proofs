import Case24992
import SignedLeaf007
import SignedLeaf013
import SignedLeaf036
import SignedLeaf053
import SignedLeaf054
import SignedLeaf055
import SignedLeaf056
import SignedLeaf059
import SignedLeaf064
import SignedLeaf075
import SignedLeaf094
import SignedLeaf096
import SignedLeaf100
import SignedLeaf102
import SignedLeaf106
import SignedLeaf108
import SignedLeaf111
import SignedLeaf113
import SignedLeaf114
import SignedLeaf115
import SignedLeaf119
import SignedLeaf124
import SignedLeaf129

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0214 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0x3fff0003fff0000000, 0x2f33bccef33bccef33bccef33bcc), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0214 : List (List Sig) := []
private def bC0214 : List (List Sig) := [sC0036, sC0215, sC0216, sC0217, sC0218, sC0219, sC0220, sC0221, sC0165, sC0222, sC0223, sC0224, sC0225, sC0226, sC0227, sC0228, sC0197, sC0229, sC0230, sC0231, sC0232, sC0233, sC0234, sC0235, sC0236, sC0237, sC0238, sC0239, sC0207, sC0240, sC0241, sC0242, sC0243, sC0244, sC0245]
theorem qC0214 : Impossible 8 1 sC0214 := by
  apply cut (us := aC0214) (bs := bC0214) (by decide +kernel)
  · decide +kernel
  · simp [aC0214]
  · intro x hx
    simp only [bC0214, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0036
    · exact qC0215
    · exact qC0216
    · exact qC0217
    · exact qC0218
    · exact qC0219
    · exact qC0220
    · exact qC0221
    · exact qC0165
    · exact qC0222
    · exact qC0223
    · exact qC0224
    · exact qC0225
    · exact qC0226
    · exact qC0227
    · exact qC0228
    · exact qC0197
    · exact qC0229
    · exact qC0230
    · exact qC0231
    · exact qC0232
    · exact qC0233
    · exact qC0234
    · exact qC0235
    · exact qC0236
    · exact qC0237
    · exact qC0238
    · exact qC0239
    · exact qC0207
    · exact qC0240
    · exact qC0241
    · exact qC0242
    · exact qC0243
    · exact qC0244
    · exact qC0245

end Lower24992
