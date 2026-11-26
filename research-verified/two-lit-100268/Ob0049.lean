import SignedSearch
import Second011
import Second012
import Second017
import Second019
import Second022
import Second031
import Second037
import Second038
import Second040
import Second045
import Second047
import Second050
import Second053
import Second054
import Second057
import Second065
import Second066
import Second068
import Second069
import Second070
import Second071
import Second073
import Second074
import Second075
import Second076

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0049 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0xffffffffffffffffff000000000, 0xff8ff8ff8ff8ff8ff8ff8ff8ff8), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0049 : List (List Sig) := []
private def bOb0049 : List (List Sig) := [sS009, sS019, sS031, sS035, sS044, sS055, sS101, sS113, sS122, sS135, sS136, sS138, sS148, sS161, sS163, sS170, sS177, sS182, sS212, sS213, sS214, sS216, sS218, sS219, sS221, sS222, sS223, sS224, sS226, sS227, sS228, sS229, sS230, sS231, sS232, sS233, sS282, sS297, sS316, sS363, sS387, sS415, sS441, sS499, sS511, sS516]
theorem qOb0049 : Impossible 8 1 sOb0049 := by
  apply cut (us := aOb0049) (bs := bOb0049) (by decide +kernel)
  · decide +kernel
  · simp [aOb0049]
  · intro x hx
    simp only [bOb0049, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS009
    · exact qS019
    · exact qS031
    · exact qS035
    · exact qS044
    · exact qS055
    · exact qS101
    · exact qS113
    · exact qS122
    · exact qS135
    · exact qS136
    · exact qS138
    · exact qS148
    · exact qS161
    · exact qS163
    · exact qS170
    · exact qS177
    · exact qS182
    · exact qS212
    · exact qS213
    · exact qS214
    · exact qS216
    · exact qS218
    · exact qS219
    · exact qS221
    · exact qS222
    · exact qS223
    · exact qS224
    · exact qS226
    · exact qS227
    · exact qS228
    · exact qS229
    · exact qS230
    · exact qS231
    · exact qS232
    · exact qS233
    · exact qS282
    · exact qS297
    · exact qS316
    · exact qS363
    · exact qS387
    · exact qS415
    · exact qS441
    · exact qS499
    · exact qS511
    · exact qS516
end Lower100268
