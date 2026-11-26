import SignedSearch
import Second003
import Second009
import Second024
import Second025
import Second033
import Second034
import Second035
import Second036
import Second037
import Second038
import Second039
import Second040
import Second041
import Second043
import Second047
import Second049
import Second050
import Second052
import Second054
import Second057
import Second058
import Second059
import Second060
import Second062
import Second064
import Second065
import Second066
import Second068
import Second069
import Second070
import Second071
import Second072
import Second074
import Second078

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0035 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000ffffffffffff000000000, 0x268e68e68e68e68e68e68e68e68e), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0035 : List (List Sig) := []
private def bOb0035 : List (List Sig) := [sS012, sS022, sS038, sS051, sS059, sS065, sS070, sS084, sS104, sS116, sS120, sS141, sS151, sS166, sS173, sS205, sS206, sS296, sS298, sS299, sS300, sS301, sS302, sS303, sS304, sS305, sS306, sS307, sS308, sS309, sS310, sS311, sS331, sS353, sS378, sS403, sS436, sS447, sS487, sS488, sS489, sS505, sS523]
theorem qOb0035 : Impossible 8 1 sOb0035 := by
  apply cut (us := aOb0035) (bs := bOb0035) (by decide +kernel)
  · decide +kernel
  · simp [aOb0035]
  · intro x hx
    simp only [bOb0035, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS012
    · exact qS022
    · exact qS038
    · exact qS051
    · exact qS059
    · exact qS065
    · exact qS070
    · exact qS084
    · exact qS104
    · exact qS116
    · exact qS120
    · exact qS141
    · exact qS151
    · exact qS166
    · exact qS173
    · exact qS205
    · exact qS206
    · exact qS296
    · exact qS298
    · exact qS299
    · exact qS300
    · exact qS301
    · exact qS302
    · exact qS303
    · exact qS304
    · exact qS305
    · exact qS306
    · exact qS307
    · exact qS308
    · exact qS309
    · exact qS310
    · exact qS311
    · exact qS331
    · exact qS353
    · exact qS378
    · exact qS403
    · exact qS436
    · exact qS447
    · exact qS487
    · exact qS488
    · exact qS489
    · exact qS505
    · exact qS523
end Lower100268
