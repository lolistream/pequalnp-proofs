import RepresentativeLowerBounds

namespace LowerDirect3
open AtlasLower

def cols111 : List W := [0xcf3cf3cf3cf3cfc000000000003f,0x30c30c30c30c3000000000ffffc0,0x3fffffff000000,0x514514514514510000003f000000,0xa28a28a28a28a200000fc0000000,0x41041041041040003f000000fc0,0x820820820820800fc000003f000,0xff000000fc003f]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row111 : lower 111 6 :=
  sound (k := 5) (xs := cols111) (samp := sample 111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols125 : List W := [0xcf3cf3cf3cf3cfc000000000003f,0x30c30c30c30c3000000000ffffc0,0x3fffffff000000,0x514514514514510000003f000000,0x20820820820820c0000fc000003f,0x820820820820820003f000000fc0,0x410410410410400fc000003f000,0x82082082082083f000000fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row125 : lower 125 7 :=
  sound (k := 6) (xs := cols125) (samp := sample 125) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols503 : List W := [0xf0f0f0f0f0f0f000000000000ff,0xf0f0f0f0f0f0f00000000000ff00,0xffffffffff0000,0x1111111111111100000000ff0000,0x22222222222222000000ff000000,0x444444444444440000ff00000000,0x8080808080808000ff00000000ff,0x8080808080808ff00000000ff00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row503 : lower 503 7 :=
  sound (k := 6) (xs := cols503) (samp := sample 503) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1242 : List W := [0xc71c71c71c71c7c0000000000fff,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x20820820820820c000000003f03f,0x4924924924924900000fc0000000,0x104104104104100003f000000fc0,0x8208208208208200fc0000fc0000,0x41041041041043f00003f000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1242 : lower 1242 8 :=
  sound (k := 7) (xs := cols1242) (samp := sample 1242) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1527 : List W := [0xc1e0f0783c1e0fc00000000001ff,0x1e0f0783c1e0f00000000003fe00,0x201008040201003ffffffffc0000,0x6231188c46231100000000000000,0x8442211088442200000007fc0000,0x884422110884400000ff8000000,0x10080402010080c01ff0000001ff,0x10080402010083fe0000003fe00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1527 : lower 1527 7 :=
  sound (k := 6) (xs := cols1527) (samp := sample 1527) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3259 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x30303030303030000000ffffff00,0xc0c0c0c0c0c0c0ffffff00000000,0x5151515151515100000000000000,0x828282828282820000000000ff00,0x202020202020200000ff000000ff,0x404040404040400ff0000ff0000,0x8080808080808ff0000ff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3259 : lower 3259 8 :=
  sound (k := 7) (xs := cols3259) (samp := sample 3259) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3311 : List W := [0xc1e0f0783c1e0fc00000000001ff,0xe070381c0e07000000007fffe00,0x30180c060301803ffffff8000000,0x5229148a45229100000000000000,0xa45229148a452200000000000000,0x884422110884400000ff8000000,0x1008040201008001ff00003fe00,0xffe00007fc01ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3311 : lower 3311 6 :=
  sound (k := 5) (xs := cols3311) (samp := sample 3311) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3503 : List W := [0xc1e0f0783c1e0fc00000000001ff,0xe070381c0e07000000007fffe00,0x30180c060301803ffffff8000000,0x5229148a45229100000000000000,0xa05028140a05020000000003fe00,0x482412090482400000ff8000000,0x9048241209048001ff000000000,0xffe00007fc01ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3503 : lower 3503 7 :=
  sound (k := 6) (xs := cols3503) (samp := sample 3503) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7543 : List W := [0x3c0f03c0f03c0ffc0000000003ff,0xc0701c0701c0700000003ffffc00,0x380e0380e038003ffffc0000000,0x4491244912449100000000000000,0x8922489224892200000000000000,0x12048120481204000000000ffc00,0x401004010040fc00ffc00003ff,0x2008020080200803ff003ff00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7543 : lower 7543 8 :=
  sound (k := 7) (xs := cols7543) (samp := sample 7543) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(111, 6), (125, 7), (503, 7), (1242, 8), (1527, 7), (3259, 8), (3311, 6), (3503, 7), (7543, 8)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row111
  · exact row125
  · exact row503
  · exact row1242
  · exact row1527
  · exact row3259
  · exact row3311
  · exact row3503
  · exact row7543
end LowerDirect3
