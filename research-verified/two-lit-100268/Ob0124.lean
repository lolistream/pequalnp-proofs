import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def sOb0124 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qOb0124 : Impossible 8 3 sOb0124 :=
  exclude_search (by decide +kernel) (by decide +kernel)
end Lower100268
