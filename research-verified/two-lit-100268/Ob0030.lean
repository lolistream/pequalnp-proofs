import SignedSearch
import Second007
import Second016
import Second017
import Second020
import Second025
import Second027
import Second036
import Second045
import Second050
import Second051
import Second053
import Second054
import Second055
import Second056
import Second058
import Second059
import Second063
import Second064
import Second066
import Second069
import Second070
import Second071
import Second072
import Second073
import Second074
import Second078

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0030 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
private def aOb0030 : List (List Sig) := []
private def bOb0030 : List (List Sig) := [sS020, sS029, sS102, sS110, sS149, sS159, sS178, sS194, sS197, sS207, sS209, sS210, sS235, sS238, sS254, sS255, sS256, sS257, sS259, sS262, sS263, sS264, sS278, sS292, sS307, sS327, sS349, sS373, sS397, sS426, sS444, sS455, sS462, sS478, sS488, sS494, sS502, sS514, sS520]
theorem qOb0030 : Impossible 8 1 sOb0030 := by
  apply cut (us := aOb0030) (bs := bOb0030) (by decide +kernel)
  · decide +kernel
  · simp [aOb0030]
  · intro x hx
    simp only [bOb0030, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS020
    · exact qS029
    · exact qS102
    · exact qS110
    · exact qS149
    · exact qS159
    · exact qS178
    · exact qS194
    · exact qS197
    · exact qS207
    · exact qS209
    · exact qS210
    · exact qS235
    · exact qS238
    · exact qS254
    · exact qS255
    · exact qS256
    · exact qS257
    · exact qS259
    · exact qS262
    · exact qS263
    · exact qS264
    · exact qS278
    · exact qS292
    · exact qS307
    · exact qS327
    · exact qS349
    · exact qS373
    · exact qS397
    · exact qS426
    · exact qS444
    · exact qS455
    · exact qS462
    · exact qS478
    · exact qS488
    · exact qS494
    · exact qS502
    · exact qS514
    · exact qS520
end Lower100268
