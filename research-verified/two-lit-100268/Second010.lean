import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS561 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xffffff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS561 : Impossible 7 2 sS561 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS568 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000ffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS568 : Impossible 7 2 sS568 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS131 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffff000000000000000, 0x0), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS131 : Impossible 7 1 sS131 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
