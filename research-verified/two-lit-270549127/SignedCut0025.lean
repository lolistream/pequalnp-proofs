import Case24992
import SignedLeaf045
import SignedLeaf068
import SignedLeaf072
import SignedLeaf087
import SignedLeaf120

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0025 : List Sig := [(0x0, 0x20008002000800200080020008), (0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
private def aC0025 : List (List Sig) := []
private def bC0025 : List (List Sig) := [sC0026, sC0027, sC0028, sC0029, sC0017, sC0030, sC0031, sC0032, sC0033, sC0034, sC0035]
theorem qC0025 : Impossible 7 1 sC0025 := by
  apply cut (us := aC0025) (bs := bC0025) (by decide +kernel)
  · decide +kernel
  · simp [aC0025]
  · intro x hx
    simp only [bC0025, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qC0026
    · exact qC0027
    · exact qC0028
    · exact qC0029
    · exact qC0017
    · exact qC0030
    · exact qC0031
    · exact qC0032
    · exact qC0033
    · exact qC0034
    · exact qC0035

end Lower24992
