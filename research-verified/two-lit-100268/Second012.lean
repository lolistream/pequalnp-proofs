import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS569 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000ffffffffffff000000000, 0x268e68e68e68e68e68e68e68e68e), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS569 : Impossible 7 2 sS569 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS211 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS211 : Impossible 7 1 sS211 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS387 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfffffffffffffff000fff000, 0x21ca1ca1ca1ca1ca1ca1ca1ca1ca), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0xffffffffffffffffff000000000, 0xff8ff8ff8ff8ff8ff8ff8ff8ff8), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS387 : Impossible 7 1 sS387 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
