import SignedSearch
import Second000
import Second002
import Second005
import Second010
import Second015
import Second018
import Second019
import Second024
import Second027
import Second028
import Second029
import Second030
import Second035
import Second036
import Second037
import Second038
import Second040
import Second042
import Second043
import Second044
import Second052
import Second055
import Second057
import Second058
import Second059
import Second060
import Second062
import Second063
import Second065
import Second066
import Second070
import Second071
import Second073
import Second075
import Second076
import Second078

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0036 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0036 : List (List Sig) := []
private def bOb0036 : List (List Sig) := [sS013, sS023, sS039, sS053, sS060, sS071, sS073, sS075, sS085, sS105, sS117, sS131, sS142, sS152, sS167, sS174, sS312, sS313, sS315, sS317, sS318, sS319, sS320, sS321, sS322, sS323, sS324, sS325, sS326, sS327, sS328, sS329, sS330, sS331, sS354, sS379, sS404, sS438, sS448, sS490, sS506, sS524, sS525, sS530]
theorem qOb0036 : Impossible 8 1 sOb0036 := by
  apply cut (us := aOb0036) (bs := bOb0036) (by decide +kernel)
  · decide +kernel
  · simp [aOb0036]
  · intro x hx
    simp only [bOb0036, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS013
    · exact qS023
    · exact qS039
    · exact qS053
    · exact qS060
    · exact qS071
    · exact qS073
    · exact qS075
    · exact qS085
    · exact qS105
    · exact qS117
    · exact qS131
    · exact qS142
    · exact qS152
    · exact qS167
    · exact qS174
    · exact qS312
    · exact qS313
    · exact qS315
    · exact qS317
    · exact qS318
    · exact qS319
    · exact qS320
    · exact qS321
    · exact qS322
    · exact qS323
    · exact qS324
    · exact qS325
    · exact qS326
    · exact qS327
    · exact qS328
    · exact qS329
    · exact qS330
    · exact qS331
    · exact qS354
    · exact qS379
    · exact qS404
    · exact qS438
    · exact qS448
    · exact qS490
    · exact qS506
    · exact qS524
    · exact qS525
    · exact qS530
end Lower100268
