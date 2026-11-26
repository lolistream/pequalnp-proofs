import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS316 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0xffffffffffffffffff000000000, 0xff8ff8ff8ff8ff8ff8ff8ff8ff8), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS316 : Impossible 7 1 sS316 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS402 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfffffffffffffff000fff000, 0x21ca1ca1ca1ca1ca1ca1ca1ca1ca), (0xfff000fff000000000fff000000, 0xfacfacfacfacfacfacfacfacfac), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS402 : Impossible 7 1 sS402 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS487 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000ffffffffffff000000000, 0x268e68e68e68e68e68e68e68e68e), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3000000fffffffffffffffffffff, 0x300f00f00f00f00f00f00f00f00f), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS487 : Impossible 7 1 sS487 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS506 : List Sig := [(0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS506 : Impossible 7 1 sS506 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS363 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0xffffffffffffffffff000000000, 0xff8ff8ff8ff8ff8ff8ff8ff8ff8), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS363 : Impossible 7 1 sS363 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS381 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000fff000000000fffffffff, 0x3687687687687687687687687687), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS381 : Impossible 7 1 sS381 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
