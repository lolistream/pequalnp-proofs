import RepresentativeLowerBounds

namespace NewMiddle1
open AtlasLower

def cols3246 : List W := [0xe1c3870e1c38700000000003fff,0x3060c183060c18000007ffffc000,0xc183060c183060fffff800000000,0x50a142850a14280000000000007f,0x83060c183060c1000000001fc000,0x244891224489120003f800000000,0x810204081020401fc000fe00000,0xfe0007f0003f80]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3246 : lower 3246 8 :=
  sound (k := 7) (xs := cols3246) (samp := sample 3246) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3511 : List W := [0xc1e0f0783c1e0fc00000000001ff,0xe070381c0e07000000007fffe00,0x30180c060301803ffffff8000000,0x5229148a45229100000000000000,0xa05028140a05020000000003fe00,0x482412090482400000ff8000000,0x8040201008040c01ff0000001ff,0x10080402010083fe00007fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3511 : lower 3511 9 :=
  sound (k := 8) (xs := cols3511) (samp := sample 3511) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7533 : List W := [0xc0e070381c0e07c000000003ffff,0x70381c0e0703800000ffffc0000,0x381c0e070381c03ffff000000000,0x4924924924924900000000000000,0x12090482412090c00000000001ff,0xa05028140a050200000007fc0000,0x4824120904824001ff000000000,0x3fe00ff803fe00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7533 : lower 7533 8 :=
  sound (k := 7) (xs := cols7533) (samp := sample 7533) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(3246, 8), (3511, 9), (7533, 8)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact row3246
  · exact row3511
  · exact row7533
end NewMiddle1
