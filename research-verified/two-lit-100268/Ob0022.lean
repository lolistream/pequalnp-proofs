import SignedSearch
import Second001
import Second016
import Second021
import Second022
import Second029
import Second033
import Second035
import Second043
import Second049
import Second051
import Second052
import Second053
import Second054
import Second058
import Second059
import Second061
import Second062
import Second067
import Second069
import Second070
import Second071
import Second073
import Second074
import Second076
import Second077

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0022 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3000000000000000000fffffffff, 0x3d2fd2fd2fd2fd2fd2fd2fd2fd2f), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0022 : List (List Sig) := [sS000, sS001]
private def bOb0022 : List (List Sig) := [sS050, sS066, sS078, sS082, sS091, sS184, sS237, sS240, sS241, sS243, sS245, sS248, sS251, sS271, sS272, sS273, sS274, sS284, sS300, sS319, sS333, sS334, sS352, sS365, sS390, sS418, sS442, sS466, sS467, sS481, sS497, sS500, sS512, sS517, sS518, sS528]
theorem qOb0022 : Impossible 8 1 sOb0022 := by
  apply cut (us := aOb0022) (bs := bOb0022) (by decide +kernel)
  · decide +kernel
  · intro x hx
    simp only [aOb0022, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact qS000
    · exact qS001
  · intro x hx
    simp only [bOb0022, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS050
    · exact qS066
    · exact qS078
    · exact qS082
    · exact qS091
    · exact qS184
    · exact qS237
    · exact qS240
    · exact qS241
    · exact qS243
    · exact qS245
    · exact qS248
    · exact qS251
    · exact qS271
    · exact qS272
    · exact qS273
    · exact qS274
    · exact qS284
    · exact qS300
    · exact qS319
    · exact qS333
    · exact qS334
    · exact qS352
    · exact qS365
    · exact qS390
    · exact qS418
    · exact qS442
    · exact qS466
    · exact qS467
    · exact qS481
    · exact qS497
    · exact qS500
    · exact qS512
    · exact qS517
    · exact qS518
    · exact qS528
end Lower100268
