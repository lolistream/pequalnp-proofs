import Case24992
import SignedLeaf025
import SignedLeaf049
import SignedLeaf059
import SignedLeaf060
import SignedLeaf064
import SignedLeaf065
import SignedLeaf068
import SignedLeaf069
import SignedLeaf070
import SignedLeaf075
import SignedLeaf083
import SignedLeaf084
import SignedLeaf090
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

def sC1018 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC1018 : List (List Sig) := [sC0657, sC0686, sC1019, sC1020, sC1021, sC1022, sC0727, sC0777, sC1023, sC0859, sC0899, sC0739]
private def bC1018 : List (List Sig) := [sC0961, sC0981, sC0996, sC1007, sC1024, sC1025, sC1026, sC1027, sC1028, sC1029, sC1030, sC0946, sC0969, sC1015, sC1031, sC1032]
theorem qC1018 : Impossible 8 2 sC1018 := by
  apply cut (us := aC1018) (bs := bC1018) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aC1018, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0657
    · exact qC0686
    · exact qC1019
    · exact qC1020
    · exact qC1021
    · exact qC1022
    · exact qC0727
    · exact qC0777
    · exact qC1023
    · exact qC0859
    · exact qC0899
    · exact qC0739
  · intro x hx
    simp only [bC1018, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0961
    · exact qC0981
    · exact qC0996
    · exact qC1007
    · exact qC1024
    · exact qC1025
    · exact qC1026
    · exact qC1027
    · exact qC1028
    · exact qC1029
    · exact qC1030
    · exact qC0946
    · exact qC0969
    · exact qC1015
    · exact qC1031
    · exact qC1032

end Lower24992
