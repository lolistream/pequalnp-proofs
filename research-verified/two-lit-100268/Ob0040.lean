import SignedSearch
import Second017
import Second024
import Second032
import Second038
import Second039
import Second040
import Second044
import Second045
import Second046
import Second048
import Second051
import Second053
import Second055
import Second057
import Second059
import Second060
import Second061
import Second062
import Second063
import Second065
import Second066
import Second067
import Second071
import Second072
import Second073
import Second075
import Second079

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0040 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0040 : List (List Sig) := []
private def bOb0040 : List (List Sig) := [sS005, sS006, sS017, sS027, sS048, sS054, sS064, sS076, sS089, sS109, sS126, sS132, sS146, sS408, sS411, sS412, sS413, sS414, sS416, sS417, sS418, sS419, sS420, sS421, sS422, sS423, sS424, sS425, sS426, sS427, sS428, sS429, sS430, sS431, sS433, sS435, sS439, sS452, sS496, sS533, sS534, sS535, sS536]
theorem qOb0040 : Impossible 8 1 sOb0040 := by
  apply cut (us := aOb0040) (bs := bOb0040) (by decide +kernel)
  · decide +kernel
  · simp [aOb0040]
  · intro x hx
    simp only [bOb0040, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS005
    · exact qS006
    · exact qS017
    · exact qS027
    · exact qS048
    · exact qS054
    · exact qS064
    · exact qS076
    · exact qS089
    · exact qS109
    · exact qS126
    · exact qS132
    · exact qS146
    · exact qS408
    · exact qS411
    · exact qS412
    · exact qS413
    · exact qS414
    · exact qS416
    · exact qS417
    · exact qS418
    · exact qS419
    · exact qS420
    · exact qS421
    · exact qS422
    · exact qS423
    · exact qS424
    · exact qS425
    · exact qS426
    · exact qS427
    · exact qS428
    · exact qS429
    · exact qS430
    · exact qS431
    · exact qS433
    · exact qS435
    · exact qS439
    · exact qS452
    · exact qS496
    · exact qS533
    · exact qS534
    · exact qS535
    · exact qS536
end Lower100268
