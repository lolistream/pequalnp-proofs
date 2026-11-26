import RepresentativeLowerBounds

namespace LowerDirect4
open AtlasLower

def cols39 : List W := [0x777777777777770ff000000000ff,0x88888888888888f0000000ffff00,0xfffff000000,0x999999999999990000000f000000,0x22222222222222f00000f0000f00,0x4444444444444400000f0000f000,0xf0f0000f000f,0xf0f0000f000f0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row39 : lower 39 5 :=
  sound (k := 4) (xs := cols39) (samp := sample 39) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols103 : List W := [0x9ce739ce739ce7fc0000000003ff,0x6318c6318c631800000001fffc00,0x3fffffe000000,0xa5294a5294a5290000003e000000,0x4a5294a5294a52000007c0000000,0x108421084210840000f800007c00,0x7c1f00000f801f,0x83e00001f003e0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row103 : lower 103 5 :=
  sound (k := 4) (xs := cols103) (samp := sample 103) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols109 : List W := [0x9ce739ce739ce7fc0000000003ff,0x6318c6318c631800000001fffc00,0x3fffffe000000,0xa5294a5294a5290000003e000000,0x421084210842107c0007c000001f,0x84210842108420000f800007c00,0x10842108421084001f00000f8000,0x83e00001f003e0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row109 : lower 109 6 :=
  sound (k := 5) (xs := cols109) (samp := sample 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols249 : List W := [0xc71c71c71c71c7c0000000000fff,0x38e38e38e38e3800000000fff000,0x3fffffff000000,0x492492492492490000003f000000,0x10410410410410c0000fc000003f,0x208208208208200003f000000fc0,0x8208208208208200fc000003f000,0x41041041041043f000000fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row249 : lower 249 7 :=
  sound (k := 6) (xs := cols249) (samp := sample 249) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1223 : List W := [0xc71c71c71c71c7c0000000000fff,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x618618618618610000000003f000,0x8a28a28a28a28a00000fc0000000,0x145145145145140003f000000000,0xc0fc0000fc003f,0x3f00003f000fc0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1223 : lower 1223 6 :=
  sound (k := 5) (xs := cols1223) (samp := sample 1223) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1487 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x7070707070707000000000ffff00,0x80808080808080ffffffff000000,0x818181818181810000000000ff00,0x12121212121212000000ff000000,0x242424242424240000ff00000000,0x4848484848484800ff0000000000,0xff000000ff00ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1487 : lower 1487 7 :=
  sound (k := 6) (xs := cols1487) (samp := sample 1487) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1494 : List W := [0xe1c3870e1c38700000000003fff,0x70e1c3870e1c380000000fffc000,0x81020408102040fffffff0000000,0x81020408102040000000001fc07f,0x12244891224489000007f0000000,0x244891224489120003f800000000,0x4081020408102001fc0000003f80,0x8102040810204fe00000fe00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1494 : lower 1494 8 :=
  sound (k := 7) (xs := cols1494) (samp := sample 1494) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3256 : List W := [0xc30c30c30c30c3c000000003ffff,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x14514514514514c000000000003f,0x2082082082082000000000fc0fc0,0x82082082082080003f00003f000,0x4104104104104100fc003f000000,0x820820820820823f000fc0000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3256 : lower 3256 8 :=
  sound (k := 7) (xs := cols3256) (samp := sample 3256) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3509 : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x4949494949494900000000000000,0x8080808080808000000000ff00ff,0x121212121212120000ff00000000,0x2020202020202000ff000000ff00,0x4040404040404ff0000ff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3509 : lower 3509 8 :=
  sound (k := 7) (xs := cols3509) (samp := sample 3509) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7535 : List W := [0x3c0f03c0f03c0ffc0000000003ff,0xc0701c0701c0700000003ffffc00,0x380e0380e038003ffffc0000000,0x4491244912449100000000000000,0x8922489224892200000000000000,0x12048120481204000000000ffc00,0x204812048120480000ffc0000000,0xffff003ff003ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7535 : lower 7535 7 :=
  sound (k := 6) (xs := cols7535) (samp := sample 7535) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(39, 5), (103, 5), (109, 6), (249, 7), (1223, 6), (1487, 7), (1494, 8), (3256, 8), (3509, 8), (7535, 7)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row39
  · exact row103
  · exact row109
  · exact row249
  · exact row1223
  · exact row1487
  · exact row1494
  · exact row3256
  · exact row3509
  · exact row7535
end LowerDirect4
