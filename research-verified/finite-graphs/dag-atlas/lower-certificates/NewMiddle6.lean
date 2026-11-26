import RepresentativeLowerBounds

namespace NewMiddle6
open AtlasLower

def cols1227 : List W := [0xc71c71c71c71c7c0000000000fff,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x618618618618610000000003f000,0x8a28a28a28a28a00000fc0000000,0x10410410410410c003f00000003f,0x410410410410400fc0000fc0000,0x3f00003f000fc0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1227 : lower 1227 8 :=
  sound (k := 7) (xs := cols1227) (samp := sample 1227) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1502 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x7070707070707000000000ffff00,0x80808080808080ffffffff000000,0x808080808080800000000000ffff,0x11111111111111000000ff000000,0x222222222222220000ff00000000,0x4444444444444400ff0000000000,0x8080808080808ff000000ff0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1502 : lower 1502 8 :=
  sound (k := 7) (xs := cols1502) (samp := sample 1502) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7548 : List W := [0xc0e070381c0e07c000000003ffff,0x70381c0e0703800000ffffc0000,0x381c0e070381c03ffff000000000,0x9048241209048c00000000001ff,0x120904824120900000000003fe00,0x6030180c06030100000007fc0000,0x84422110884422001ff000000000,0x8040201008043fe00ff8000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7548 : lower 7548 9 :=
  sound (k := 8) (xs := cols7548) (samp := sample 7548) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def rows : List (ℕ × ℕ) := [(1227, 8), (1502, 8), (7548, 9)]
theorem checked : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact row1227
  · exact row1502
  · exact row7548
end NewMiddle6
