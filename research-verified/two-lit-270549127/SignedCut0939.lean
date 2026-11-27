import Case24992
import SignedLeaf070
import SignedLeaf071
import SignedLeaf074
import SignedLeaf086
import SignedLeaf094
import SignedLeaf095
import SignedLeaf108
import SignedLeaf116

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0939 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffc00000000000003ffffffffff, 0x291fa47e91fa47e91fa47e91fa47)]
private def aC0939 : List (List Sig) := [sC0940, sC0675, sC0764, sC0804, sC0845, sC0885, sC0736]
private def bC0939 : List (List Sig) := [sC0941, sC0942, sC0943, sC0944, sC0945, sC0946]
theorem qC0939 : Impossible 8 2 sC0939 := by
  apply cut (us := aC0939) (bs := bC0939) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC0939, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0940
    · exact qC0675
    · exact qC0764
    · exact qC0804
    · exact qC0845
    · exact qC0885
    · exact qC0736
  · intro x hx
    simp only [bC0939, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0941
    · exact qC0942
    · exact qC0943
    · exact qC0944
    · exact qC0945
    · exact qC0946

end Lower24992
