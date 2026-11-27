import Case24992
import SignedCut0006
import SignedCut0108
import SignedCut0134
import SignedCut0157
import SignedCut0180
import SignedCut0214
import SignedCut0246
import SignedCut0267
import SignedCut0299
import SignedCut0329
import SignedCut0352
import SignedCut0383
import SignedCut0412
import SignedCut0438
import SignedCut0464
import SignedCut0493
import SignedCut0520
import SignedCut0546
import SignedCut0572
import SignedCut0595
import SignedLeaf000
import SignedLeaf001
import SignedLeaf012
import SignedLeaf013
import SignedLeaf014
import SignedLeaf015
import SignedLeaf016
import SignedLeaf017
import SignedLeaf018
import SignedLeaf019
import SignedLeaf024
import SignedLeaf025
import SignedLeaf029
import SignedLeaf030
import SignedLeaf032
import SignedLeaf033
import SignedLeaf034
import SignedLeaf042
import SignedLeaf043

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0001 : List Sig := [(0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x0, 0x2913a44e913a44e913a44e913a44)]
private def aC0001 : List (List Sig) := []
private def bC0001 : List (List Sig) := [sC0002, sC0003, sC0004, sC0005, sC0006, sC0102, sC0103, sC0104, sC0105, sC0106, sC0107, sC0108, sC0133, sC0134, sC0157, sC0180, sC0214, sC0246, sC0267, sC0297, sC0298, sC0299, sC0327, sC0328, sC0329, sC0352, sC0379, sC0380, sC0381, sC0382, sC0383, sC0412, sC0438, sC0464, sC0493, sC0520, sC0546, sC0572, sC0595]
theorem qC0001 : Impossible 9 1 sC0001 := by
  apply cut (us := aC0001) (bs := bC0001) (by decide +kernel)
  · decide +kernel
  · simp [aC0001]
  · intro x hx
    simp only [bC0001, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0002
    · exact qC0003
    · exact qC0004
    · exact qC0005
    · exact qC0006
    · exact qC0102
    · exact qC0103
    · exact qC0104
    · exact qC0105
    · exact qC0106
    · exact qC0107
    · exact qC0108
    · exact qC0133
    · exact qC0134
    · exact qC0157
    · exact qC0180
    · exact qC0214
    · exact qC0246
    · exact qC0267
    · exact qC0297
    · exact qC0298
    · exact qC0299
    · exact qC0327
    · exact qC0328
    · exact qC0329
    · exact qC0352
    · exact qC0379
    · exact qC0380
    · exact qC0381
    · exact qC0382
    · exact qC0383
    · exact qC0412
    · exact qC0438
    · exact qC0464
    · exact qC0493
    · exact qC0520
    · exact qC0546
    · exact qC0572
    · exact qC0595

end Lower24992
