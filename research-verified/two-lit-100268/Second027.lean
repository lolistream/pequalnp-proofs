import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS379 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS379 : Impossible 7 1 sS379 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS410 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000000000000000000000000, 0x0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000fff000fffffffff000fff, 0x3e3fe3fe3fe3fe3fe3fe3fe3fe3f), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS410 : Impossible 7 1 sS410 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS450 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfffffffffffffff000000, 0x2d2ad2ad2ad2ad2ad2ad2ad2ad2a), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS450 : Impossible 7 1 sS450 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS548 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000ffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS548 : Impossible 7 2 sS548 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS263 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000ffffff000000ffffff, 0x1f01f01f01f01f01f01f01f01f0), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS263 : Impossible 7 1 sS263 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
