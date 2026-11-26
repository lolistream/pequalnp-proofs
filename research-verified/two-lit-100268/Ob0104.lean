import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def sOb0104 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffff000fffffffff000, 0x3fcffcffcffcffcffcffcffcffcf), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007)]
theorem qOb0104 : Impossible 8 2 sOb0104 :=
  exclude_search (by decide +kernel) (by decide +kernel)
end Lower100268
