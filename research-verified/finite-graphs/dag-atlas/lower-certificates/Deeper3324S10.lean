import AtlasCut

namespace CutWords3324
open AtlasLower AtlasMemo
set_option maxRecDepth 14000
set_option maxHeartbeats 9500000

def s10 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]

private def z10c0 : State := [0x202020202020200000000000000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e0 : optimized 6 0 z10c0 = false := by decide +kernel

private def z10c1 : State := [0x202020202020200ff0000ff0000, 0x404040404040400000000000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e1 : optimized 6 0 z10c1 = false := by decide +kernel

private def z10c2 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c000000000000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e2 : optimized 6 0 z10c2 = false := by decide +kernel

private def z10c3 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xdfdfdfdfdfdfdf0000000000ffff]
private theorem e3 : optimized 6 0 z10c3 = false := by decide +kernel

private def z10c4 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc2c2c2c2c2c2c2ffffff00ff0000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e4 : optimized 6 0 z10c4 = false := by decide +kernel

private def z10c5 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc4c4c4c4c4c4c4ffffffff000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e5 : optimized 6 0 z10c5 = false := by decide +kernel

private def z10c6 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xd8d8d8d8d8d8d80000000000ffff, 0xe1e1e1e1e1e1e1ffffff00000000]
private theorem e6 : optimized 6 0 z10c6 = false := by decide +kernel

private def z10c7 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xd8d8d8d8d8d8d80000000000ffff, 0xf8f8f8f8f8f8f8ffffffffff0000]
private theorem e7 : optimized 6 0 z10c7 = false := by decide +kernel

private def z10c8 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x3a3a3a3a3a3a3a00ff00ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e8 : optimized 6 0 z10c8 = false := by decide +kernel

private def z10c9 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x3c3c3c3c3c3c3cff0000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e9 : optimized 6 0 z10c9 = false := by decide +kernel

private def z10c10 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff, 0xe1e1e1e1e1e1e1ffffff00000000]
private theorem e10 : optimized 6 0 z10c10 = false := by decide +kernel

private def z10c11 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x38383838383838000000ffff0000, 0xd8d8d8d8d8d8d80000000000ffff, 0xe1e1e1e1e1e1e1ffffff00000000]
private theorem e11 : optimized 6 1 z10c11 = false := by decide +kernel

private def z10c12 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff, 0xdfdfdfdfdfdfdf0000000000ffff]
private theorem e12 : optimized 6 0 z10c12 = false := by decide +kernel

private def z10c13 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xdfdfdfdfdfdfdf0000000000ffff]
private theorem e13 : optimized 6 1 z10c13 = false := by decide +kernel

private def z10c14 : State := [0x202020202020200ff0000ff0000, 0x6060606060606ffff00ffff0000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e14 : optimized 6 0 z10c14 = false := by decide +kernel

private def z10c15 : State := [0x202020202020200ff0000ff0000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x25252525252525ff00ffff000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e15 : optimized 6 0 z10c15 = false := by decide +kernel

private def z10c16 : State := [0x202020202020200ff0000ff0000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x3c3c3c3c3c3c3cff0000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e16 : optimized 6 0 z10c16 = false := by decide +kernel

private def z10c17 : State := [0x202020202020200ff0000ff0000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xc4c4c4c4c4c4c4ffffffff000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e17 : optimized 6 0 z10c17 = false := by decide +kernel

private def z10c18 : State := [0x202020202020200ff0000ff0000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc4c4c4c4c4c4c4ffffffff000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e18 : optimized 6 1 z10c18 = false := by decide +kernel

private def z10c19 : State := [0x202020202020200ff0000ff0000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x3c3c3c3c3c3c3cff0000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e19 : optimized 6 1 z10c19 = false := by decide +kernel

private def z10c20 : State := [0x4040404040404ff0000ff000000, 0x6060606060606ffff00ffff0000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e20 : optimized 6 0 z10c20 = false := by decide +kernel

private def z10c21 : State := [0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x2323232323232300ffff00ff0000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e21 : optimized 6 0 z10c21 = false := by decide +kernel

private def z10c22 : State := [0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x3a3a3a3a3a3a3a00ff00ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e22 : optimized 6 0 z10c22 = false := by decide +kernel

private def z10c23 : State := [0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xc2c2c2c2c2c2c2ffffff00ff0000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e23 : optimized 6 0 z10c23 = false := by decide +kernel

private def z10c24 : State := [0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc2c2c2c2c2c2c2ffffff00ff0000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e24 : optimized 6 1 z10c24 = false := by decide +kernel

private def z10c25 : State := [0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x3a3a3a3a3a3a3a00ff00ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e25 : optimized 6 1 z10c25 = false := by decide +kernel

private def z10c26 : State := [0x6060606060606ffff00ffff0000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xd8d8d8d8d8d8d80000000000ffff]
private theorem e26 : optimized 6 1 z10c26 = false := by decide +kernel

private def next : Layer := #[z10c0,z10c1,z10c2,z10c3,z10c4,z10c5,z10c6,z10c7,z10c8,z10c9,z10c10,z10c11,z10c12,z10c13,z10c14,z10c15,z10c16,z10c17,z10c18,z10c19,z10c20,z10c21,z10c22,z10c23,z10c24,z10c25,z10c26]
private theorem afterStep : AtlasCut.Anchors 6 next := by
  intro s mem nd
  simp only [next, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact AtlasCut.leaf e0 nd
  · exact AtlasCut.leaf e1 nd
  · exact AtlasCut.leaf e2 nd
  · exact AtlasCut.leaf e3 nd
  · exact AtlasCut.leaf e4 nd
  · exact AtlasCut.leaf e5 nd
  · exact AtlasCut.leaf e6 nd
  · exact AtlasCut.leaf e7 nd
  · exact AtlasCut.leaf e8 nd
  · exact AtlasCut.leaf e9 nd
  · exact AtlasCut.leaf e10 nd
  · exact AtlasCut.leaf e11 nd
  · exact AtlasCut.leaf e12 nd
  · exact AtlasCut.leaf e13 nd
  · exact AtlasCut.leaf e14 nd
  · exact AtlasCut.leaf e15 nd
  · exact AtlasCut.leaf e16 nd
  · exact AtlasCut.leaf e17 nd
  · exact AtlasCut.leaf e18 nd
  · exact AtlasCut.leaf e19 nd
  · exact AtlasCut.leaf e20 nd
  · exact AtlasCut.leaf e21 nd
  · exact AtlasCut.leaf e22 nd
  · exact AtlasCut.leaf e23 nd
  · exact AtlasCut.leaf e24 nd
  · exact AtlasCut.leaf e25 nd
  · exact AtlasCut.leaf e26 nd
private theorem completeStep : (#[s10] : Layer).all (stateOK next 7) = true := by decide +kernel
theorem node10 : s10.Nodup → ¬ live basicOps goal 7 s10.toFinset :=
  (AtlasCut.step afterStep completeStep) s10 (by simp)

end CutWords3324
