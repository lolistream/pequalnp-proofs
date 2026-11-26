import RepresentativeLowerBounds

namespace NewHigh13
open AtlasLower

def cols3262 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x30303030303030000000ffffff00,0xc0c0c0c0c0c0c0ffffff00000000,0x50505050505050000000000000ff,0x818181818181810000000000ff00,0x222222222222220000ff00000000,0x404040404040400ff0000ff0000,0x8080808080808ff0000ff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3262 : lower 3262 9 :=
  sound (k := 8) (xs := cols3262) (samp := sample 3262) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(3262, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl
  · exact row3262
end NewHigh13
