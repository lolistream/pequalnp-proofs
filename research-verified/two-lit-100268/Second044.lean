import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS380 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xffffffffffff000000ffffff000, 0xfecfecfecfecfecfecfecfecfec), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS380 : Impossible 7 1 sS380 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS552 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS552 : Impossible 7 2 sS552 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS563 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfffffffffffffff000000, 0x2d2ad2ad2ad2ad2ad2ad2ad2ad2a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS563 : Impossible 7 2 sS563 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS328 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000fff000fff, 0xd38d38d38d38d38d38d38d38d38)]
theorem qS328 : Impossible 7 1 sS328 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS435 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000ffffffffffff000000000, 0x268e68e68e68e68e68e68e68e68e), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS435 : Impossible 7 1 sS435 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS493 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3000000fffffffffffffffffffff, 0x300f00f00f00f00f00f00f00f00f), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS493 : Impossible 7 1 sS493 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS504 : List Sig := [(0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xfff000fff000000000fff000000, 0xfacfacfacfacfacfacfacfacfac), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS504 : Impossible 7 1 sS504 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
