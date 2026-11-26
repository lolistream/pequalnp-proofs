import RepresentativeLowerBounds

namespace NewHigh11
open AtlasLower

def cols3479 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x30303030303030000000ffffff00,0xc0c0c0c0c0c0c0ffffff00000000,0x414141414141410000000000ff00,0x8282828282828200000000ff0000,0x141414141414140000ff00000000,0x2020202020202000ff00000000ff,0x8080808080808ff0000ff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3479 : lower 3479 9 :=
  sound (k := 8) (xs := cols3479) (samp := sample 3479) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(3479, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl
  · exact row3479
end NewHigh11
