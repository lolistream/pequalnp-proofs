import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS270 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fffffffffffffffffffff000fff, 0x2d3ad3ad3ad3ad3ad3ad3ad3ad3a)]
theorem qS270 : Impossible 7 1 sS270 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS404 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfffffffffffffff000fff000, 0x21ca1ca1ca1ca1ca1ca1ca1ca1ca), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS404 : Impossible 7 1 sS404 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS460 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000000000000000000000000, 0x0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000000000fffffffff, 0x1ff5ff5ff5ff5ff5ff5ff5ff5ff5), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS460 : Impossible 7 1 sS460 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS490 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3000000fffffffffffffffffffff, 0x300f00f00f00f00f00f00f00f00f), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS490 : Impossible 7 1 sS490 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS160 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000000000, 0x0), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS160 : Impossible 7 1 sS160 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
