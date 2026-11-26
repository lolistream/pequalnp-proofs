import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS503 : List Sig := [(0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS503 : Impossible 7 1 sS503 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS400 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfffffffffffffff000fff000, 0x21ca1ca1ca1ca1ca1ca1ca1ca1ca), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS400 : Impossible 7 1 sS400 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS447 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfffffffffffffff000000, 0x2d2ad2ad2ad2ad2ad2ad2ad2ad2a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000ffffffffffff000000000, 0x268e68e68e68e68e68e68e68e68e), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS447 : Impossible 7 1 sS447 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS555 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xfff000000000000000000000000, 0x0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS555 : Impossible 7 2 sS555 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS562 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfffffffffffffff000000, 0x2d2ad2ad2ad2ad2ad2ad2ad2ad2a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000000000000000000000000, 0x0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS562 : Impossible 7 2 sS562 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS079 : List Sig := [(0xfff000, 0x2002002002002002002002002002), (0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfffffffffffffff000fff000, 0x21ca1ca1ca1ca1ca1ca1ca1ca1ca), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS079 : Impossible 7 1 sS079 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
