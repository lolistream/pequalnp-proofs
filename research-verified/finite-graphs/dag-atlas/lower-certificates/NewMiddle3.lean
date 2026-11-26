import RepresentativeLowerBounds

namespace NewMiddle3
open AtlasLower

def cols1241 : List W := [0xc71c71c71c71c7c0000000000fff,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x618618618618610000000003f000,0x8208208208208c0000fc000003f,0x104104104104100003f000000fc0,0x8208208208208200fc0000fc0000,0x41041041041043f00003f000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1241 : lower 1241 8 :=
  sound (k := 7) (xs := cols1241) (samp := sample 1241) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3309 : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x4949494949494900000000000000,0x90909090909090000000000000ff,0x222222222222220000ff00000000,0x404040404040400ff0000ff0000,0xff0000ff00ff00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3309 : lower 3309 8 :=
  sound (k := 7) (xs := cols3309) (samp := sample 3309) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3518 : List W := [0xc1e0f0783c1e0fc00000000001ff,0xe070381c0e07000000007fffe00,0x30180c060301803ffffff8000000,0x12090482412090c00000000001ff,0x6030180c0603010000000003fe00,0x8442211088442200000ff8000000,0x8844221108844001ff000000000,0x10080402010083fe00007fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3518 : lower 3518 9 :=
  sound (k := 8) (xs := cols3518) (samp := sample 3518) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(1241, 8), (3309, 8), (3518, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact row1241
  · exact row3309
  · exact row3518
end NewMiddle3
