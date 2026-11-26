import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS198 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000000000000000000000000, 0x0), (0x3fff000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS198 : Impossible 7 1 sS198 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS232 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0xffffffffffffffffff000000000, 0xff8ff8ff8ff8ff8ff8ff8ff8ff8), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS232 : Impossible 7 1 sS232 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS329 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS329 : Impossible 7 1 sS329 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS062 : List Sig := [(0x0, 0x2002002002002002002002002002), (0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS062 : Impossible 7 1 sS062 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
