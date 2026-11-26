import SignedSearch
import Second009
import Second019
import Second020
import Second021
import Second023
import Second026
import Second027
import Second029
import Second036
import Second037
import Second044
import Second045
import Second050
import Second051
import Second053
import Second055
import Second056
import Second060
import Second061
import Second063
import Second064
import Second065
import Second066
import Second067
import Second068
import Second070
import Second072
import Second073
import Second077
import Second079

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0038 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0038 : List (List Sig) := []
private def bOb0038 : List (List Sig) := [sS003, sS015, sS025, sS046, sS052, sS062, sS087, sS097, sS107, sS119, sS124, sS144, sS154, sS357, sS358, sS359, sS360, sS361, sS362, sS364, sS365, sS366, sS367, sS368, sS369, sS370, sS371, sS372, sS373, sS374, sS375, sS376, sS377, sS378, sS380, sS381, sS407, sS430, sS450, sS493, sS527, sS528, sS529]
theorem qOb0038 : Impossible 8 1 sOb0038 := by
  apply cut (us := aOb0038) (bs := bOb0038) (by decide +kernel)
  · decide +kernel
  · simp [aOb0038]
  · intro x hx
    simp only [bOb0038, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS003
    · exact qS015
    · exact qS025
    · exact qS046
    · exact qS052
    · exact qS062
    · exact qS087
    · exact qS097
    · exact qS107
    · exact qS119
    · exact qS124
    · exact qS144
    · exact qS154
    · exact qS357
    · exact qS358
    · exact qS359
    · exact qS360
    · exact qS361
    · exact qS362
    · exact qS364
    · exact qS365
    · exact qS366
    · exact qS367
    · exact qS368
    · exact qS369
    · exact qS370
    · exact qS371
    · exact qS372
    · exact qS373
    · exact qS374
    · exact qS375
    · exact qS376
    · exact qS377
    · exact qS378
    · exact qS380
    · exact qS381
    · exact qS407
    · exact qS430
    · exact qS450
    · exact qS493
    · exact qS527
    · exact qS528
    · exact qS529
end Lower100268
