import Case24992
import SignedCut0012
import SignedLeaf020
import SignedLeaf029
import SignedLeaf032
import SignedLeaf040
import SignedLeaf044
import SignedLeaf045
import SignedLeaf046
import SignedLeaf047
import SignedLeaf049
import SignedLeaf051
import SignedLeaf054
import SignedLeaf061
import SignedLeaf062
import SignedLeaf063
import SignedLeaf066
import SignedLeaf067
import SignedLeaf071
import SignedLeaf072
import SignedLeaf076
import SignedLeaf078
import SignedLeaf090
import SignedLeaf092
import SignedLeaf096
import SignedLeaf097
import SignedLeaf102
import SignedLeaf104
import SignedLeaf106
import SignedLeaf109
import SignedLeaf115
import SignedLeaf116

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0464 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0464 : List (List Sig) := []
private def bC0464 : List (List Sig) := [sC0465, sC0466, sC0467, sC0012, sC0468, sC0469, sC0470, sC0471, sC0472, sC0473, sC0474, sC0475, sC0138, sC0161, sC0193, sC0227, sC0255, sC0280, sC0476, sC0477, sC0478, sC0479, sC0480, sC0365, sC0481, sC0482, sC0483, sC0484, sC0404, sC0433, sC0459, sC0485, sC0486, sC0487, sC0488, sC0489, sC0211, sC0243, sC0294, sC0377, sC0410, sC0490, sC0491, sC0492]
theorem qC0464 : Impossible 8 1 sC0464 := by
  apply cut (us := aC0464) (bs := bC0464) (by decide +kernel)
  · decide +kernel
  · simp [aC0464]
  · intro x hx
    simp only [bC0464, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0465
    · exact qC0466
    · exact qC0467
    · exact qC0012
    · exact qC0468
    · exact qC0469
    · exact qC0470
    · exact qC0471
    · exact qC0472
    · exact qC0473
    · exact qC0474
    · exact qC0475
    · exact qC0138
    · exact qC0161
    · exact qC0193
    · exact qC0227
    · exact qC0255
    · exact qC0280
    · exact qC0476
    · exact qC0477
    · exact qC0478
    · exact qC0479
    · exact qC0480
    · exact qC0365
    · exact qC0481
    · exact qC0482
    · exact qC0483
    · exact qC0484
    · exact qC0404
    · exact qC0433
    · exact qC0459
    · exact qC0485
    · exact qC0486
    · exact qC0487
    · exact qC0488
    · exact qC0489
    · exact qC0211
    · exact qC0243
    · exact qC0294
    · exact qC0377
    · exact qC0410
    · exact qC0490
    · exact qC0491
    · exact qC0492

end Lower24992
