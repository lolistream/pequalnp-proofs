import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def sOb0055 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000fff000fffffffff000fff, 0x3e3fe3fe3fe3fe3fe3fe3fe3fe3f), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qOb0055 : Impossible 8 1 sOb0055 :=
  exclude_search (by decide +kernel) (by decide +kernel)
end Lower100268
