import Case24992
import SignedLeaf009
import SignedLeaf034
import SignedLeaf037
import SignedLeaf038
import SignedLeaf040
import SignedLeaf048
import SignedLeaf050
import SignedLeaf052
import SignedLeaf055
import SignedLeaf058
import SignedLeaf062
import SignedLeaf063
import SignedLeaf072
import SignedLeaf077
import SignedLeaf078
import SignedLeaf079
import SignedLeaf082
import SignedLeaf083
import SignedLeaf086
import SignedLeaf088
import SignedLeaf097
import SignedLeaf098
import SignedLeaf101
import SignedLeaf102
import SignedLeaf103
import SignedLeaf108
import SignedLeaf110
import SignedLeaf111
import SignedLeaf115
import SignedLeaf116
import SignedLeaf124

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0520 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0x2f33bccef33bccef33bccef33bcc), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0520 : List (List Sig) := []
private def bC0520 : List (List Sig) := [sC0521, sC0522, sC0523, sC0524, sC0525, sC0526, sC0527, sC0528, sC0529, sC0119, sC0530, sC0531, sC0142, sC0532, sC0195, sC0533, sC0287, sC0534, sC0535, sC0318, sC0536, sC0537, sC0348, sC0367, sC0538, sC0539, sC0540, sC0541, sC0406, sC0435, sC0542, sC0486, sC0514, sC0370, sC0543, sC0544, sC0213, sC0295, sC0325, sC0491, sC0518, sC0545]
theorem qC0520 : Impossible 8 1 sC0520 := by
  apply cut (us := aC0520) (bs := bC0520) (by decide +kernel)
  · decide +kernel
  · simp [aC0520]
  · intro x hx
    simp only [bC0520, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0521
    · exact qC0522
    · exact qC0523
    · exact qC0524
    · exact qC0525
    · exact qC0526
    · exact qC0527
    · exact qC0528
    · exact qC0529
    · exact qC0119
    · exact qC0530
    · exact qC0531
    · exact qC0142
    · exact qC0532
    · exact qC0195
    · exact qC0533
    · exact qC0287
    · exact qC0534
    · exact qC0535
    · exact qC0318
    · exact qC0536
    · exact qC0537
    · exact qC0348
    · exact qC0367
    · exact qC0538
    · exact qC0539
    · exact qC0540
    · exact qC0541
    · exact qC0406
    · exact qC0435
    · exact qC0542
    · exact qC0486
    · exact qC0514
    · exact qC0370
    · exact qC0543
    · exact qC0544
    · exact qC0213
    · exact qC0295
    · exact qC0325
    · exact qC0491
    · exact qC0518
    · exact qC0545

end Lower24992
