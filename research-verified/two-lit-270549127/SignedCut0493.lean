import Case24992
import SignedCut0025
import SignedLeaf021
import SignedLeaf030
import SignedLeaf033
import SignedLeaf044
import SignedLeaf045
import SignedLeaf046
import SignedLeaf048
import SignedLeaf049
import SignedLeaf054
import SignedLeaf055
import SignedLeaf062
import SignedLeaf063
import SignedLeaf066
import SignedLeaf067
import SignedLeaf071
import SignedLeaf072
import SignedLeaf078
import SignedLeaf093
import SignedLeaf094
import SignedLeaf097
import SignedLeaf100
import SignedLeaf102
import SignedLeaf104
import SignedLeaf106
import SignedLeaf109
import SignedLeaf116

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0493 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0493 : List (List Sig) := []
private def bC0493 : List (List Sig) := [sC0494, sC0495, sC0496, sC0497, sC0025, sC0498, sC0499, sC0500, sC0501, sC0502, sC0503, sC0504, sC0140, sC0163, sC0194, sC0228, sC0256, sC0505, sC0506, sC0317, sC0507, sC0508, sC0509, sC0366, sC0510, sC0511, sC0512, sC0513, sC0405, sC0434, sC0460, sC0485, sC0514, sC0515, sC0516, sC0517, sC0212, sC0244, sC0324, sC0378, sC0411, sC0490, sC0518, sC0519]
theorem qC0493 : Impossible 8 1 sC0493 := by
  apply cut (us := aC0493) (bs := bC0493) (by decide +kernel)
  · decide +kernel
  · simp [aC0493]
  · intro x hx
    simp only [bC0493, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0494
    · exact qC0495
    · exact qC0496
    · exact qC0497
    · exact qC0025
    · exact qC0498
    · exact qC0499
    · exact qC0500
    · exact qC0501
    · exact qC0502
    · exact qC0503
    · exact qC0504
    · exact qC0140
    · exact qC0163
    · exact qC0194
    · exact qC0228
    · exact qC0256
    · exact qC0505
    · exact qC0506
    · exact qC0317
    · exact qC0507
    · exact qC0508
    · exact qC0509
    · exact qC0366
    · exact qC0510
    · exact qC0511
    · exact qC0512
    · exact qC0513
    · exact qC0405
    · exact qC0434
    · exact qC0460
    · exact qC0485
    · exact qC0514
    · exact qC0515
    · exact qC0516
    · exact qC0517
    · exact qC0212
    · exact qC0244
    · exact qC0324
    · exact qC0378
    · exact qC0411
    · exact qC0490
    · exact qC0518
    · exact qC0519

end Lower24992
