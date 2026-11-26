import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def sOb0111 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030), (0x3ffffffffffffffffff000ffffff, 0x32d72d72d72d72d72d72d72d72d7)]
theorem qOb0111 : Impossible 8 2 sOb0111 :=
  exclude_search (by decide +kernel) (by decide +kernel)
end Lower100268
