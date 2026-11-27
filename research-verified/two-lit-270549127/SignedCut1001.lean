import Case24992
import SignedLeaf024
import SignedLeaf046
import SignedLeaf059
import SignedLeaf060
import SignedLeaf064
import SignedLeaf065
import SignedLeaf069
import SignedLeaf070
import SignedLeaf075
import SignedLeaf083
import SignedLeaf084
import SignedLeaf089
import SignedLeaf091
import SignedLeaf095
import SignedLeaf107
import SignedLeaf114
import SignedLeaf118
import SignedLeaf120

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC1001 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC1001 : List (List Sig) := [sC0656, sC0685, sC1002, sC1003, sC1004, sC1005, sC0726, sC1006, sC0817, sC0858, sC0898, sC0738]
private def bC1001 : List (List Sig) := [sC0960, sC0980, sC0995, sC1007, sC1008, sC1009, sC1010, sC1011, sC1012, sC1013, sC1014, sC0945, sC0968, sC1015, sC1016, sC1017]
theorem qC1001 : Impossible 8 2 sC1001 := by
  apply cut (us := aC1001) (bs := bC1001) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC1001, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0656
    · exact qC0685
    · exact qC1002
    · exact qC1003
    · exact qC1004
    · exact qC1005
    · exact qC0726
    · exact qC1006
    · exact qC0817
    · exact qC0858
    · exact qC0898
    · exact qC0738
  · intro x hx
    simp only [bC1001, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0960
    · exact qC0980
    · exact qC0995
    · exact qC1007
    · exact qC1008
    · exact qC1009
    · exact qC1010
    · exact qC1011
    · exact qC1012
    · exact qC1013
    · exact qC1014
    · exact qC0945
    · exact qC0968
    · exact qC1015
    · exact qC1016
    · exact qC1017

end Lower24992
