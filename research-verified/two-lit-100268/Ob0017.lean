import SignedSearch
import Second002
import Second003
import Second004
import Second005
import Second006
import Second007
import Second008
import Second009
import Second011
import Second014
import Second016
import Second019
import Second020
import Second021
import Second022
import Second023
import Second024
import Second025
import Second030
import Second033
import Second036
import Second042
import Second046
import Second047
import Second055
import Second056
import Second057
import Second058
import Second066
import Second071
import Second076

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sOb0017 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000000000000000000000000, 0x0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
private def aOb0017 : List (List Sig) := []
private def bOb0017 : List (List Sig) := [sS008, sS018, sS034, sS056, sS067, sS080, sS100, sS112, sS137, sS147, sS162, sS169, sS176, sS179, sS180, sS183, sS184, sS185, sS186, sS188, sS191, sS192, sS193, sS194, sS196, sS197, sS198, sS204, sS295, sS314, sS341, sS355, sS359, sS384, sS409, sS437, sS440, sS458, sS459, sS486, sS498, sS508, sS509]
theorem qOb0017 : Impossible 8 1 sOb0017 := by
  apply cut (us := aOb0017) (bs := bOb0017) (by decide +kernel)
  · decide +kernel
  · simp [aOb0017]
  · intro x hx
    simp only [bOb0017, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qS008
    · exact qS018
    · exact qS034
    · exact qS056
    · exact qS067
    · exact qS080
    · exact qS100
    · exact qS112
    · exact qS137
    · exact qS147
    · exact qS162
    · exact qS169
    · exact qS176
    · exact qS179
    · exact qS180
    · exact qS183
    · exact qS184
    · exact qS185
    · exact qS186
    · exact qS188
    · exact qS191
    · exact qS192
    · exact qS193
    · exact qS194
    · exact qS196
    · exact qS197
    · exact qS198
    · exact qS204
    · exact qS295
    · exact qS314
    · exact qS341
    · exact qS355
    · exact qS359
    · exact qS384
    · exact qS409
    · exact qS437
    · exact qS440
    · exact qS458
    · exact qS459
    · exact qS486
    · exact qS498
    · exact qS508
    · exact qS509
end Lower100268
