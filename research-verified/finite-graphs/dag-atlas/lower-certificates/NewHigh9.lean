import RepresentativeLowerBounds

namespace NewHigh9
open AtlasLower

def cols3258 : List W := [0xe1c3870e1c38700000000003fff,0x3060c183060c18000007ffffc000,0xc183060c183060fffff800000000,0x50a142850a14280000000000007f,0x83060c183060c1000000001fc000,0x204081020408100003f800003f80,0x408102040810201fc000fe00000,0x8102040810204fe0007f0000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3258 : lower 3258 9 :=
  sound (k := 8) (xs := cols3258) (samp := sample 3258) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(3258, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl
  · exact row3258
end NewHigh9
