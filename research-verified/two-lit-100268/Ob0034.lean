import SignedSearch
import Second017
import Second026
import Second029
import Second030
import Second035
import Second037
import Second043
import Second044
import Second045
import Second048
import Second050
import Second051
import Second054
import Second056
import Second058
import Second059
import Second060
import Second061
import Second063
import Second064
import Second065
import Second068
import Second069
import Second070
import Second072
import Second077
import Second078

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0034 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000fff000000, 0xfacfacfacfacfacfacfacfacfac), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0034 : List (List Sig) := []
private def bOb0034 : List (List Sig) := [sS011, sS021, sS037, sS043, sS058, sS069, sS083, sS092, sS103, sS115, sS128, sS140, sS150, sS165, sS172, sS202, sS203, sS280, sS281, sS283, sS284, sS285, sS286, sS287, sS288, sS289, sS290, sS291, sS292, sS293, sS294, sS311, sS330, sS352, sS377, sS402, sS434, sS446, sS485, sS504, sS529]
theorem qOb0034 : Impossible 8 1 sOb0034 := by
  apply cut (us := aOb0034) (bs := bOb0034) (by decide +kernel)
  · decide +kernel
  · simp [aOb0034]
  · intro x hx
    simp only [bOb0034, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS011
    · exact qS021
    · exact qS037
    · exact qS043
    · exact qS058
    · exact qS069
    · exact qS083
    · exact qS092
    · exact qS103
    · exact qS115
    · exact qS128
    · exact qS140
    · exact qS150
    · exact qS165
    · exact qS172
    · exact qS202
    · exact qS203
    · exact qS280
    · exact qS281
    · exact qS283
    · exact qS284
    · exact qS285
    · exact qS286
    · exact qS287
    · exact qS288
    · exact qS289
    · exact qS290
    · exact qS291
    · exact qS292
    · exact qS293
    · exact qS294
    · exact qS311
    · exact qS330
    · exact qS352
    · exact qS377
    · exact qS402
    · exact qS434
    · exact qS446
    · exact qS485
    · exact qS504
    · exact qS529
end Lower100268
