import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS436 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000ffffffffffff000000000, 0x268e68e68e68e68e68e68e68e68e), (0xffffffffffffffffff000fff000, 0x27ce7ce7ce7ce7ce7ce7ce7ce7ce), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS436 : Impossible 7 1 sS436 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS448 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xfffffffffffffff000000, 0x2d2ad2ad2ad2ad2ad2ad2ad2ad2a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS448 : Impossible 7 1 sS448 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS337 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3000fff000ffffffffffffffffff, 0x397b97b97b97b97b97b97b97b97b), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS337 : Impossible 7 1 sS337 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS433 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000000, 0xfacfacfacfacfacfacfacfacfac), (0xffffffffffff000000000fff000, 0x7c47c47c47c47c47c47c47c47c4), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS433 : Impossible 7 1 sS433 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS507 : List Sig := [(0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000ffffff000, 0xde8de8de8de8de8de8de8de8de8), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000fff000000000fffffffff, 0x3687687687687687687687687687), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS507 : Impossible 7 1 sS507 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS515 : List Sig := [(0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0xfff000fff000000000fff000000, 0xfacfacfacfacfacfacfacfacfac), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS515 : Impossible 7 1 sS515 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS019 : List Sig := [(0x0, 0x20020020020020020020020020), (0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0xffffffffffffffffff000000000, 0xff8ff8ff8ff8ff8ff8ff8ff8ff8), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS019 : Impossible 7 1 sS019 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
