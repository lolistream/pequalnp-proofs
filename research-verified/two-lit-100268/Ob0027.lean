import SignedSearch
import Second014
import Second015
import Second018
import Second029
import Second030
import Second032
import Second036
import Second039
import Second045
import Second047
import Second048
import Second051
import Second052
import Second053
import Second055
import Second056
import Second058
import Second061
import Second062
import Second067
import Second069
import Second071
import Second072
import Second076
import Second077
import Second078

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0027 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030), (0x3ffffff000000fff000fffffffff, 0x3037037037037037037037037037)]
private def aOb0027 : List (List Sig) := []
private def bOb0027 : List (List Sig) := [sS095, sS111, sS155, sS156, sS157, sS192, sS199, sS200, sS201, sS234, sS236, sS251, sS252, sS253, sS257, sS258, sS260, sS261, sS262, sS274, sS275, sS276, sS277, sS289, sS305, sS323, sS345, sS356, sS370, sS395, sS422, sS443, sS475, sS484, sS501, sS513, sS519, sS521]
theorem qOb0027 : Impossible 8 1 sOb0027 := by
  apply cut (us := aOb0027) (bs := bOb0027) (by decide +kernel)
  · decide +kernel
  · simp [aOb0027]
  · intro x hx
    simp only [bOb0027, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS095
    · exact qS111
    · exact qS155
    · exact qS156
    · exact qS157
    · exact qS192
    · exact qS199
    · exact qS200
    · exact qS201
    · exact qS234
    · exact qS236
    · exact qS251
    · exact qS252
    · exact qS253
    · exact qS257
    · exact qS258
    · exact qS260
    · exact qS261
    · exact qS262
    · exact qS274
    · exact qS275
    · exact qS276
    · exact qS277
    · exact qS289
    · exact qS305
    · exact qS323
    · exact qS345
    · exact qS356
    · exact qS370
    · exact qS395
    · exact qS422
    · exact qS443
    · exact qS475
    · exact qS484
    · exact qS501
    · exact qS513
    · exact qS519
    · exact qS521
end Lower100268
