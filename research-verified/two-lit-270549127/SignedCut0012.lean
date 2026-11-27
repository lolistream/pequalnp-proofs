import Case24992
import SignedLeaf044
import SignedLeaf067
import SignedLeaf068
import SignedLeaf071
import SignedLeaf072
import SignedLeaf087
import SignedLeaf102

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0012 : List Sig := [(0x0, 0x20008002000800200080020008), (0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0012 : List (List Sig) := []
private def bC0012 : List (List Sig) := [sC0013, sC0014, sC0015, sC0016, sC0017, sC0018, sC0019, sC0020, sC0021, sC0022, sC0023]
theorem qC0012 : Impossible 7 1 sC0012 := by
  apply cut (us := aC0012) (bs := bC0012) (by decide +kernel)
  · decide +kernel
  · simp [aC0012]
  · intro x hx
    simp only [bC0012, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0013
    · exact qC0014
    · exact qC0015
    · exact qC0016
    · exact qC0017
    · exact qC0018
    · exact qC0019
    · exact qC0020
    · exact qC0021
    · exact qC0022
    · exact qC0023

end Lower24992
