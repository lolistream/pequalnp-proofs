import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sS279 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3fff000fff000000000fffffffff, 0x3687687687687687687687687687), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS279 : Impossible 7 1 sS279 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS351 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000fff000000000fffffffff, 0x3687687687687687687687687687), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS351 : Impossible 7 1 sS351 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS432 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000000000000, 0x684684684684684684684684684), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000fff000fffffffff000fff, 0x3e3fe3fe3fe3fe3fe3fe3fe3fe3f), (0x3ffffffffffffffffff000000fff, 0x203a03a03a03a03a03a03a03a03a)]
theorem qS432 : Impossible 7 1 sS432 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS311 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xfff000fffffffffffffff000000, 0x2faefaefaefaefaefaefaefaefae), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS311 : Impossible 7 1 sS311 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS330 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0xffffffffffff000000ffffff000, 0xfecfecfecfecfecfecfecfecfec), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS330 : Impossible 7 1 sS330 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS333 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3000000000000000000fffffffff, 0x3d2fd2fd2fd2fd2fd2fd2fd2fd2f), (0x3fff000fff000000000fffffffff, 0x3687687687687687687687687687), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS333 : Impossible 7 1 sS333 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sS352 : List Sig := [(0xfff000000, 0xd28d28d28d28d28d28d28d28d28), (0xffffffffffff000000000, 0x200a00a00a00a00a00a00a00a00a), (0xfff000fff000000000fff000, 0x1c01c01c01c01c01c01c01c01c0), (0x3000000000000000000fffffffff, 0x3007007007007007007007007007), (0x3fff000fff000000000fffffffff, 0x3faffaffaffaffaffaffaffaffaf), (0x3ffffff000000fff000000000fff, 0x30030030030030030030030030)]
theorem qS352 : Impossible 7 1 sS352 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower100268
