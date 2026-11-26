import RepresentativeLowerBounds

namespace NewHigh10
open AtlasLower

def cols1495 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x7070707070707000000000ffff00,0x80808080808080ffffffff000000,0x818181818181810000000000ff00,0x12121212121212000000ff000000,0x242424242424240000ff00000000,0x4040404040404000ff00000000ff,0x8080808080808ff000000ff0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1495 : lower 1495 9 :=
  sound (k := 8) (xs := cols1495) (samp := sample 1495) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(1495, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl
  · exact row1495
end NewHigh10
