import SignedSearch
import Second006
import Second008
import Second016
import Second023
import Second026
import Second031
import Second032
import Second034
import Second035
import Second036
import Second037
import Second040
import Second041
import Second045
import Second050
import Second052
import Second053
import Second054
import Second055
import Second057
import Second059
import Second060
import Second061
import Second062
import Second064
import Second065
import Second066
import Second068
import Second069
import Second071
import Second079

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0039 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfffffffffffffff000fff000, 0x21ca1ca1ca1ca1ca1ca1ca1ca1ca), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0039 : List (List Sig) := []
private def bOb0039 : List (List Sig) := [sS004, sS016, sS026, sS042, sS047, sS063, sS079, sS088, sS108, sS125, sS129, sS145, sS158, sS382, sS383, sS384, sS385, sS386, sS388, sS389, sS390, sS391, sS392, sS393, sS394, sS395, sS396, sS397, sS398, sS399, sS400, sS401, sS402, sS403, sS405, sS406, sS407, sS431, sS451, sS494, sS495, sS531, sS532]
theorem qOb0039 : Impossible 8 1 sOb0039 := by
  apply cut (us := aOb0039) (bs := bOb0039) (by decide +kernel)
  · decide +kernel
  · simp [aOb0039]
  · intro x hx
    simp only [bOb0039, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS004
    · exact qS016
    · exact qS026
    · exact qS042
    · exact qS047
    · exact qS063
    · exact qS079
    · exact qS088
    · exact qS108
    · exact qS125
    · exact qS129
    · exact qS145
    · exact qS158
    · exact qS382
    · exact qS383
    · exact qS384
    · exact qS385
    · exact qS386
    · exact qS388
    · exact qS389
    · exact qS390
    · exact qS391
    · exact qS392
    · exact qS393
    · exact qS394
    · exact qS395
    · exact qS396
    · exact qS397
    · exact qS398
    · exact qS399
    · exact qS400
    · exact qS401
    · exact qS402
    · exact qS403
    · exact qS405
    · exact qS406
    · exact qS407
    · exact qS431
    · exact qS451
    · exact qS494
    · exact qS495
    · exact qS531
    · exact qS532
end Lower100268
