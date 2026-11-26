import RepresentativeLowerBounds

namespace LowerDirect2
open AtlasLower

def cols101 : List W := [0x33333333333333fff00000000fff,0xcccccccccccccc00000000fff000,0xfffff000000,0x555555555555550000000f000000,0x8888888888888800f000f000000f,0x2222222222222200000f0000f000,0xf00f0000f00f0,0xf00f0000f00f00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row101 : lower 101 5 :=
  sound (k := 4) (xs := cols101) (samp := sample 101) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1093 : List W := [0x33333333333333fff00000000fff,0x444444444444440000000ffff000,0x88888888888888000ffff0000000,0x999999999999990000000000f000,0x4444444444444400f000f000000f,0x2222222222222200000f000f0000,0xf00f000f000f0,0xf00f000f000f00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1093 : lower 1093 6 :=
  sound (k := 5) (xs := cols1093) (samp := sample 1093) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1132 : List W := [0x8c6318c6318c63fc000000007fff,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x5294a5294a52947c00000000001f,0x21084210842108800007c00003e0,0x842108421084210000f8000f8000,0x8421084210842001f0001f00000,0x3e0003e007c00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1132 : lower 1132 7 :=
  sound (k := 6) (xs := cols1132) (samp := sample 1132) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1135 : List W := [0x1e3c78f1e3c78f0000000000007f,0x60c183060c18300000000fffff80,0x81020408102040fffffff0000000,0xa3468d1a3468d100000000000000,0x44891224489122000007f0000000,0x81020408102040003f800003f80,0x1020408102040801fc00001fc000,0xfe00000fe0007f]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1135 : lower 1135 6 :=
  sound (k := 5) (xs := cols1135) (samp := sample 1135) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1226 : List W := [0x8c6318c6318c63fc000000007fff,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x421084210842107c0000000f801f,0x94a5294a5294a5000007c0000000,0x210842108421088000f8000003e0,0x8421084210842001f0001f00000,0x3e0003e007c00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1226 : lower 1226 7 :=
  sound (k := 6) (xs := cols1226) (samp := sample 1226) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1230 : List W := [0xc71c71c71c71c7c0000000000fff,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x20820820820820c000000003f03f,0x4924924924924900000fc0000000,0x924924924924920003f000000000,0x410410410410400fc0000fc0000,0x3f00003f000fc0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1230 : lower 1230 7 :=
  sound (k := 6) (xs := cols1230) (samp := sample 1230) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1259 : List W := [0xe1c3870e1c38700000000003fff,0x70e1c3870e1c380000000fffc000,0x81020408102040fffffff0000000,0x93264c993264c900000000000000,0x24489122448912000007f0000000,0x408102040810200003f80000007f,0x810204081020401fc00001fc000,0xfe00000fe03f80]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1259 : lower 1259 6 :=
  sound (k := 5) (xs := cols1259) (samp := sample 1259) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1275 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x7070707070707000000000ffff00,0x80808080808080ffffffff000000,0x9191919191919100000000000000,0x22222222222222000000ff000000,0x404040404040400000ff000000ff,0x404040404040400ff000000ff00,0x8080808080808ff000000ff0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1275 : lower 1275 7 :=
  sound (k := 6) (xs := cols1275) (samp := sample 1275) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3238 : List W := [0xc30c30c30c30c3c000000003ffff,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x14514514514514c000000000003f,0x6186186186186100000000fc0000,0x8a28a28a28a28a0003f000000000,0xfc003f000fc0,0x3f000fc003f000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3238 : lower 3238 7 :=
  sound (k := 6) (xs := cols3238) (samp := sample 3238) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3321 : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x4949494949494900000000000000,0x90909090909090000000000000ff,0x202020202020200000ff0000ff00,0x202020202020200ff0000ff0000,0x4040404040404ff0000ff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3321 : lower 3321 8 :=
  sound (k := 7) (xs := cols3321) (samp := sample 3321) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(101, 5), (1093, 6), (1132, 7), (1135, 6), (1226, 7), (1230, 7), (1259, 6), (1275, 7), (3238, 7), (3321, 8)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row101
  · exact row1093
  · exact row1132
  · exact row1135
  · exact row1226
  · exact row1230
  · exact row1259
  · exact row1275
  · exact row3238
  · exact row3321
end LowerDirect2
