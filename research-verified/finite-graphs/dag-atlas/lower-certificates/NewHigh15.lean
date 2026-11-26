import RepresentativeLowerBounds

namespace NewHigh15
open AtlasLower

def cols3516 : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x48484848484848000000000000ff,0x8080808080808000000000ffff00,0x111111111111110000ff00000000,0x2222222222222200ff0000000000,0x4040404040404ff0000ff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3516 : lower 3516 9 :=
  sound (k := 8) (xs := cols3516) (samp := sample 3516) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(3516, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl
  · exact row3516
end NewHigh15
