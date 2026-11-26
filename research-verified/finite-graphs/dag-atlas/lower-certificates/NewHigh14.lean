import RepresentativeLowerBounds

namespace NewHigh14
open AtlasLower

def cols7675 : List W := [0x80f01e03c0780f7ff000000007ff,0xf01e03c0780f0800000003ff800,0x700e01c0380700000fffffc00000,0x9112224448891100000000000000,0x2224448891122200000000000000,0x440881102204407ff000000007ff,0x8410821042084000001ffc00000,0x801002004008800ffe003ff800]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7675 : lower 7675 9 :=
  sound (k := 8) (xs := cols7675) (samp := sample 7675) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(7675, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl
  · exact row7675
end NewHigh14
