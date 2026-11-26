import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS446 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfffffffffffffff000000, 0x2d2ad2ad2ad2ad2ad2ad2ad2ad2a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000fff000000, 0xfacfacfacfacfacfacfacfacfac), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS446 : Impossible 7 1 sS446 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS310 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000ffffffffffff000000000, 0x268e68e68e68e68e68e68e68e68e), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS310 : Impossible 7 1 sS310 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS406 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfffffffffffffff000fff000, 0x21ca1ca1ca1ca1ca1ca1ca1ca1ca), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000fff000000000fffffffff, 0x3687687687687687687687687687), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS406 : Impossible 7 1 sS406 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS466 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3000000000000000000fffffffff, 0x3d2fd2fd2fd2fd2fd2fd2fd2fd2f), (0x3000000fffffffffffffffffffff, 0x300f00f00f00f00f00f00f00f00f), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS466 : Impossible 7 1 sS466 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS560 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS560 : Impossible 7 2 sS560 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS322 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030), (0x3ffffff000000fff000fff000fff, 0xd38d38d38d38d38d38d38d38d38)]
theorem qS322 : Impossible 7 1 sS322 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
