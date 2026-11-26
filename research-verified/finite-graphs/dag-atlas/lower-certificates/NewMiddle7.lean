import RepresentativeLowerBounds

namespace NewMiddle7
open AtlasLower

def cols3308 : List W := [0x60c183060c183000000001fffff,0x3870e1c3870e1c000007ffe00000,0xc183060c183060fffff800000000,0x489122448912240000000000007f,0x9122448912244800000000003f80,0x224489122448910003f800000000,0x408102040810201fc000fe00000,0xfe0007f01fc000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3308 : lower 3308 8 :=
  sound (k := 7) (xs := cols3308) (samp := sample 3308) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7541 : List W := [0xc0e070381c0e07c000000003ffff,0x70381c0e0703800000ffffc0000,0x381c0e070381c03ffff000000000,0x4924924924924900000000000000,0x12090482412090c00000000001ff,0xa05028140a050200000007fc0000,0x4020100804020001ff00003fe00,0x8040201008043fe00ff8000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7541 : lower 7541 9 :=
  sound (k := 8) (xs := cols7541) (samp := sample 7541) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(3308, 8), (7541, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact row3308
  · exact row7541
end NewMiddle7
