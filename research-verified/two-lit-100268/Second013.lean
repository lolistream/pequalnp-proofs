import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS340 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000000000000000000000fff, 0x0), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS340 : Impossible 7 1 sS340 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS510 : List Sig := [(0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000000000000000000000000, 0x0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030), (0x3ffffffffffffffffff000ffffff, 0x32d72d72d72d72d72d72d72d72d7)]
theorem qS510 : Impossible 7 1 sS510 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS522 : List Sig := [(0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a), (0x3ffffffffffffffffff000ffffff, 0x32d72d72d72d72d72d72d72d72d7)]
theorem qS522 : Impossible 7 1 sS522 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
