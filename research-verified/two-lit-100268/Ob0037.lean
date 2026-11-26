import SignedSearch
import Second013
import Second015
import Second018
import Second032
import Second035
import Second037
import Second038
import Second039
import Second040
import Second041
import Second043
import Second047
import Second048
import Second049
import Second051
import Second052
import Second056
import Second062
import Second063
import Second064
import Second067
import Second068
import Second072
import Second073
import Second074
import Second075
import Second076
import Second077
import Second078

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0037 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000fff000000000fffffffff, 0x3687687687687687687687687687), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0037 : List (List Sig) := []
private def bOb0037 : List (List Sig) := [sS014, sS024, sS040, sS061, sS072, sS077, sS086, sS096, sS106, sS118, sS130, sS143, sS153, sS168, sS175, sS332, sS333, sS335, sS336, sS339, sS340, sS342, sS343, sS344, sS345, sS346, sS347, sS348, sS349, sS350, sS351, sS352, sS353, sS354, sS356, sS381, sS406, sS449, sS491, sS507, sS526]
theorem qOb0037 : Impossible 8 1 sOb0037 := by
  apply cut (us := aOb0037) (bs := bOb0037) (by decide +kernel)
  · decide +kernel
  · simp [aOb0037]
  · intro x hx
    simp only [bOb0037, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS014
    · exact qS024
    · exact qS040
    · exact qS061
    · exact qS072
    · exact qS077
    · exact qS086
    · exact qS096
    · exact qS106
    · exact qS118
    · exact qS130
    · exact qS143
    · exact qS153
    · exact qS168
    · exact qS175
    · exact qS332
    · exact qS333
    · exact qS335
    · exact qS336
    · exact qS339
    · exact qS340
    · exact qS342
    · exact qS343
    · exact qS344
    · exact qS345
    · exact qS346
    · exact qS347
    · exact qS348
    · exact qS349
    · exact qS350
    · exact qS351
    · exact qS352
    · exact qS353
    · exact qS354
    · exact qS356
    · exact qS381
    · exact qS406
    · exact qS449
    · exact qS491
    · exact qS507
    · exact qS526
end Lower100268
