import RepresentativeLowerBounds

namespace LowerDirect1
open AtlasLower

def cols47 : List W := [0xbdef7bdef7bdef7c00000000001f,0x4210842108421080000001ffffe0,0x3fffffe000000,0xc6318c6318c6310000003e000000,0x8421084210842800007c00003e0,0x108421084210840000f800007c00,0x21084210842108001f00000f8000,0x7fe00001f0001f]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row47 : lower 47 6 :=
  sound (k := 5) (xs := cols47) (samp := sample 47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols239 : List W := [0x1e3c78f1e3c78f0000000000007f,0xe1c3870e1c3870000000001fff80,0xffffffffe00000,0x224489122448910000000fe00000,0x44891224489122000007f0000000,0x891224489122440003f800000000,0x1020408102040801fc0000003f80,0xfe0000001fc07f]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row239 : lower 239 6 :=
  sound (k := 5) (xs := cols239) (samp := sample 239) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1101 : List W := [0x9ce739ce739ce7fc0000000003ff,0x210842108421080000003ffffc00,0x4210842108421003ffffc0000000,0xc6318c6318c63100000000007c00,0x210842108421087c0007c000001f,0x84210842108420000f8000f8000,0x10842108421084001f0001f00000,0x83e0003e0003e0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1101 : lower 1101 7 :=
  sound (k := 6) (xs := cols1101) (samp := sample 1101) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1127 : List W := [0xc71c71c71c71c7c0000000000fff,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x69a69a69a69a6900000000000000,0x9249249249249200000fc0000000,0x41041041041040003f00003f000,0xc0fc0000fc003f,0x3f00003f000fc0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1127 : lower 1127 5 :=
  sound (k := 4) (xs := cols1127) (samp := sample 1127) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1246 : List W := [0x1e3c78f1e3c78f0000000000007f,0x60c183060c18300000000fffff80,0x81020408102040fffffff0000000,0x8102040810204000000000003fff,0x22448912244891000007f0000000,0x448912244891220003f800000000,0x810204081020401fc00001fc000,0x10204081020408fe00000fe00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1246 : lower 1246 8 :=
  sound (k := 7) (xs := cols1246) (samp := sample 1246) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1263 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x7070707070707000000000ffff00,0x80808080808080ffffffff000000,0x9191919191919100000000000000,0x22222222222222000000ff000000,0x444444444444440000ff00000000,0x808080808080800ff000000ff00,0xff000000ff00ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1263 : lower 1263 6 :=
  sound (k := 5) (xs := cols1263) (samp := sample 1263) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3243 : List W := [0xe1c3870e1c38700000000003fff,0x3060c183060c18000007ffffc000,0xc183060c183060fffff800000000,0x52a54a952a54a900000000000000,0x850a142850a142000000001fc000,0x204081020408100003f80000007f,0x810204081020401fc000fe00000,0xfe0007f0003f80]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3243 : lower 3243 7 :=
  sound (k := 6) (xs := cols3243) (samp := sample 3243) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3471 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x30303030303030000000ffffff00,0xc0c0c0c0c0c0c0ffffff00000000,0x414141414141410000000000ff00,0x8282828282828200000000ff0000,0x141414141414140000ff00000000,0x2828282828282800ff0000000000,0xff0000ff0000ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3471 : lower 3471 7 :=
  sound (k := 6) (xs := cols3471) (samp := sample 3471) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3517 : List W := [0xc1e0f0783c1e0fc00000000001ff,0xe070381c0e07000000007fffe00,0x30180c060301803ffffff8000000,0x5229148a45229100000000000000,0x20100804020100c000000003ffff,0x8442211088442200000ff8000000,0x8844221108844001ff000000000,0x10080402010083fe00007fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3517 : lower 3517 8 :=
  sound (k := 7) (xs := cols3517) (samp := sample 3517) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3575 : List W := [0x3c0f03c0f03c0ffc0000000003ff,0xc0f03c0f03c0f0000000000ffc00,0x300c0300c030003fffffff00000,0x4511445114451100000000000000,0x8a2288a2288a2200000000000000,0x104411044110440000003ff00000,0x802008020080fc00ffc00003ff,0x2008020080200803ff00000ffc00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3575 : lower 3575 7 :=
  sound (k := 6) (xs := cols3575) (samp := sample 3575) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(47, 6), (239, 6), (1101, 7), (1127, 5), (1246, 8), (1263, 6), (3243, 7), (3471, 7), (3517, 8), (3575, 7)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row47
  · exact row239
  · exact row1101
  · exact row1127
  · exact row1246
  · exact row1263
  · exact row3243
  · exact row3471
  · exact row3517
  · exact row3575
end LowerDirect1
