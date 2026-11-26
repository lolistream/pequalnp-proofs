import SignedSearch
import Second006
import Second009
import Second012
import Second014
import Second019
import Second020
import Second021
import Second022
import Second024
import Second026
import Second028
import Second033
import Second034
import Second035
import Second038
import Second040
import Second043
import Second047
import Second049
import Second050
import Second052
import Second053
import Second054
import Second055
import Second056
import Second057
import Second058
import Second060
import Second061
import Second066
import Second072
import Second077

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0032 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
private def aOb0032 : List (List Sig) := []
private def bOb0032 : List (List Sig) := [sS002, sS010, sS030, sS032, sS036, sS045, sS057, sS068, sS081, sS114, sS123, sS139, sS160, sS164, sS171, sS208, sS211, sS215, sS217, sS220, sS239, sS241, sS242, sS244, sS247, sS265, sS266, sS268, sS269, sS270, sS279, sS294, sS310, sS329, sS351, sS375, sS400, sS428, sS445, sS456, sS463, sS489, sS495, sS503, sS515]
theorem qOb0032 : Impossible 8 1 sOb0032 := by
  apply cut (us := aOb0032) (bs := bOb0032) (by decide +kernel)
  · decide +kernel
  · simp [aOb0032]
  · intro x hx
    simp only [bOb0032, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS002
    · exact qS010
    · exact qS030
    · exact qS032
    · exact qS036
    · exact qS045
    · exact qS057
    · exact qS068
    · exact qS081
    · exact qS114
    · exact qS123
    · exact qS139
    · exact qS160
    · exact qS164
    · exact qS171
    · exact qS208
    · exact qS211
    · exact qS215
    · exact qS217
    · exact qS220
    · exact qS239
    · exact qS241
    · exact qS242
    · exact qS244
    · exact qS247
    · exact qS265
    · exact qS266
    · exact qS268
    · exact qS269
    · exact qS270
    · exact qS279
    · exact qS294
    · exact qS310
    · exact qS329
    · exact qS351
    · exact qS375
    · exact qS400
    · exact qS428
    · exact qS445
    · exact qS456
    · exact qS463
    · exact qS489
    · exact qS495
    · exact qS503
    · exact qS515
end Lower100268
