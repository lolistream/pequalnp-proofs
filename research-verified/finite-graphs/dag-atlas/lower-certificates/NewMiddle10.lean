import RepresentativeLowerBounds

namespace NewMiddle10
open AtlasLower

def cols1103 : List W := [0xcf3cf3cf3cf3cfc000000000003f,0x104104104104100000003fffffc0,0x208208208208203fffffc0000000,0x6186186186186100000000000fc0,0x9249249249249200000fc0000000,0x41041041041040003f00003f000,0x820820820820800fc0000fc0000,0xff00003f00003f]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1103 : lower 1103 8 :=
  sound (k := 7) (xs := cols1103) (samp := sample 1103) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1134 : List W := [0xc71c71c71c71c7c0000000000fff,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x28a28a28a28a28c000000000003f,0x5145145145145100000fc0000000,0x820820820820820003f00003f000,0x410410410410400fc0000fc0000,0x3f00003f000fc0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1134 : lower 1134 8 :=
  sound (k := 7) (xs := cols1134) (samp := sample 1134) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(1103, 8), (1134, 8)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact row1103
  · exact row1134
end NewMiddle10
