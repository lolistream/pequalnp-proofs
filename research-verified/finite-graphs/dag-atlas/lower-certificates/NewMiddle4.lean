import RepresentativeLowerBounds

namespace NewMiddle4
open AtlasLower

def cols1117 : List W := [0xcf3cf3cf3cf3cfc000000000003f,0x104104104104100000003fffffc0,0x208208208208203fffffc0000000,0x6186186186186100000000000fc0,0x10410410410410c0000fc000003f,0x820820820820820003f00003f000,0x410410410410400fc0000fc0000,0x82082082082083f00003f000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1117 : lower 1117 8 :=
  sound (k := 7) (xs := cols1117) (samp := sample 1117) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3247 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x30303030303030000000ffffff00,0xc0c0c0c0c0c0c0ffffff00000000,0x5151515151515100000000000000,0x828282828282820000000000ff00,0x242424242424240000ff00000000,0x808080808080800ff0000ff0000,0xff0000ff0000ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3247 : lower 3247 8 :=
  sound (k := 7) (xs := cols3247) (samp := sample 3247) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3477 : List W := [0xe1c3870e1c38700000000003fff,0x3060c183060c18000007ffffc000,0xc183060c183060fffff800000000,0x42850a142850a1000000001fc000,0x810204081020400000000fe0007f,0x142850a142850a0003f800000000,0x2040810204081001fc0000003f80,0x8102040810204fe0007f0000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3477 : lower 3477 9 :=
  sound (k := 8) (xs := cols3477) (samp := sample 3477) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(1117, 8), (3247, 8), (3477, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact row1117
  · exact row3247
  · exact row3477
end NewMiddle4
