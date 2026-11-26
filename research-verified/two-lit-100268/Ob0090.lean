import SignedSearch
import Second008
import Second012
import Second013
import Second019
import Second020
import Second025
import Second030
import Second032
import Second035
import Second036
import Second038
import Second039
import Second041
import Second043
import Second044
import Second045
import Second048
import Second049
import Second051
import Second052
import Second054
import Second055
import Second056
import Second058
import Second062

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0090 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
private def aOb0090 : List (List Sig) := [sS098, sS099, sS225, sS232, sS246, sS249, sS250, sS267, sS337, sS432, sS482, sS522]
private def bOb0090 : List (List Sig) := [sS544, sS545, sS546, sS547, sS549, sS551, sS553, sS556, sS558, sS560, sS563, sS564, sS567, sS569, sS570, sS572, sS575]
theorem qOb0090 : Impossible 8 2 sOb0090 := by
  apply cut (us := aOb0090) (bs := bOb0090) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aOb0090, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS098
    · exact qS099
    · exact qS225
    · exact qS232
    · exact qS246
    · exact qS249
    · exact qS250
    · exact qS267
    · exact qS337
    · exact qS432
    · exact qS482
    · exact qS522
  · intro x hx
    simp only [bOb0090, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS544
    · exact qS545
    · exact qS546
    · exact qS547
    · exact qS549
    · exact qS551
    · exact qS553
    · exact qS556
    · exact qS558
    · exact qS560
    · exact qS563
    · exact qS564
    · exact qS567
    · exact qS569
    · exact qS570
    · exact qS572
    · exact qS575
end Lower100268
