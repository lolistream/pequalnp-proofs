import RepresentativeLowerBounds

namespace NewMiddle9
open AtlasLower

def cols1095 : List W := [0x9ce739ce739ce7fc0000000003ff,0x210842108421080000003ffffc00,0x4210842108421003ffffc0000000,0xc6318c6318c63100000000007c00,0x294a5294a5294a000007c0000000,0x108421084210840000f8000f8000,0x7c1f0001f0001f,0x83e0003e0003e0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1095 : lower 1095 7 :=
  sound (k := 6) (xs := cols1095) (samp := sample 1095) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1262 : List W := [0xe1c3870e1c38700000000003fff,0x70e1c3870e1c380000000fffc000,0x81020408102040fffffff0000000,0x912244891224480000000000007f,0x22448912244891000007f0000000,0x448912244891220003f800000000,0x810204081020401fc00001fc000,0xfe00000fe03f80]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1262 : lower 1262 8 :=
  sound (k := 7) (xs := cols1262) (samp := sample 1262) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3510 : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x48484848484848000000000000ff,0x8181818181818100000000ff0000,0x121212121212120000ff00000000,0x2020202020202000ff000000ff00,0x4040404040404ff0000ff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3510 : lower 3510 9 :=
  sound (k := 8) (xs := cols3510) (samp := sample 3510) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(1095, 7), (1262, 8), (3510, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact row1095
  · exact row1262
  · exact row3510
end NewMiddle9
