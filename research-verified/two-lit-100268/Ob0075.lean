import SignedSearch
import Second001
import Second007
import Second010
import Second013
import Second015
import Second016
import Second022
import Second027
import Second028
import Second031
import Second032
import Second033
import Second034
import Second039
import Second041
import Second042
import Second044
import Second047
import Second052
import Second054
import Second056
import Second057
import Second058
import Second070

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0075 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000000000000000000000000, 0x0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0075 : List (List Sig) := [sS133, sS134, sS181, sS182, sS187, sS189, sS190, sS195, sS338, sS410, sS460, sS510]
private def bOb0075 : List (List Sig) := [sS540, sS541, sS542, sS543, sS548, sS550, sS552, sS554, sS555, sS557, sS559, sS561, sS562, sS565, sS566, sS568, sS571, sS573, sS574]
theorem qOb0075 : Impossible 8 2 sOb0075 := by
  apply cut (us := aOb0075) (bs := bOb0075) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aOb0075, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS133
    · exact qS134
    · exact qS181
    · exact qS182
    · exact qS187
    · exact qS189
    · exact qS190
    · exact qS195
    · exact qS338
    · exact qS410
    · exact qS460
    · exact qS510
  · intro x hx
    simp only [bOb0075, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS540
    · exact qS541
    · exact qS542
    · exact qS543
    · exact qS548
    · exact qS550
    · exact qS552
    · exact qS554
    · exact qS555
    · exact qS557
    · exact qS559
    · exact qS561
    · exact qS562
    · exact qS565
    · exact qS566
    · exact qS568
    · exact qS571
    · exact qS573
    · exact qS574
end Lower100268
