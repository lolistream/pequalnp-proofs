import SignedSearch
import Second011
import Second018
import Second021
import Second023
import Second028
import Second029
import Second030
import Second035
import Second040
import Second044
import Second048
import Second049
import Second053
import Second055
import Second056
import Second057
import Second067
import Second068
import Second069
import Second072
import Second073
import Second074
import Second075
import Second077
import Second078
import Second079

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0042 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3000000fffffffffffffffffffff, 0x300f00f00f00f00f00f00f00f00f), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0042 : List (List Sig) := []
private def bOb0042 : List (List Sig) := [sS007, sS028, sS033, sS041, sS049, sS074, sS090, sS093, sS094, sS121, sS127, sS453, sS454, sS457, sS459, sS461, sS464, sS465, sS466, sS468, sS469, sS470, sS471, sS472, sS473, sS474, sS475, sS476, sS477, sS479, sS480, sS481, sS483, sS484, sS485, sS490, sS491, sS492, sS493, sS496, sS537, sS538, sS539]
theorem qOb0042 : Impossible 8 1 sOb0042 := by
  apply cut (us := aOb0042) (bs := bOb0042) (by decide +kernel)
  · decide +kernel
  · simp [aOb0042]
  · intro x hx
    simp only [bOb0042, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS007
    · exact qS028
    · exact qS033
    · exact qS041
    · exact qS049
    · exact qS074
    · exact qS090
    · exact qS093
    · exact qS094
    · exact qS121
    · exact qS127
    · exact qS453
    · exact qS454
    · exact qS457
    · exact qS459
    · exact qS461
    · exact qS464
    · exact qS465
    · exact qS466
    · exact qS468
    · exact qS469
    · exact qS470
    · exact qS471
    · exact qS472
    · exact qS473
    · exact qS474
    · exact qS475
    · exact qS476
    · exact qS477
    · exact qS479
    · exact qS480
    · exact qS481
    · exact qS483
    · exact qS484
    · exact qS485
    · exact qS490
    · exact qS491
    · exact qS492
    · exact qS493
    · exact qS496
    · exact qS537
    · exact qS538
    · exact qS539
end Lower100268
