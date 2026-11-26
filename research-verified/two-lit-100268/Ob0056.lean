import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def sOb0056 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000000000fffffffff, 0x1ff5ff5ff5ff5ff5ff5ff5ff5ff5), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qOb0056 : Impossible 8 1 sOb0056 :=
  exclude_search (by decide +kernel) (by decide +kernel)
end Lower100268
