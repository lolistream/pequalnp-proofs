import AtlasCut

namespace CutWords3324
open AtlasLower AtlasMemo
set_option maxRecDepth 14000
set_option maxHeartbeats 9500000

def s18 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]

private def z18c0 : State := [0x202020202020200000000000000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e0 : optimized 6 0 z18c0 = false := by decide +kernel

private def z18c1 : State := [0x202020202020200ff0000ff0000, 0x404040404040400000000000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e1 : optimized 6 0 z18c1 = false := by decide +kernel

private def z18c2 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc2c2c2c2c2c2c2ffffff00ff0000]
private theorem e2 : optimized 6 0 z18c2 = false := by decide +kernel

private def z18c3 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc4c4c4c4c4c4c4ffffffff000000]
private theorem e3 : optimized 6 0 z18c3 = false := by decide +kernel

private def z18c4 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xe1e1e1e1e1e1e1ffffff00000000]
private theorem e4 : optimized 6 0 z18c4 = false := by decide +kernel

private def z18c5 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xf8f8f8f8f8f8f8ffffffffff0000]
private theorem e5 : optimized 6 0 z18c5 = false := by decide +kernel

private def z18c6 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0xc0c0c0c0c0c0c0ffffff00000000, 0xdfdfdfdfdfdfdf0000000000ffff]
private theorem e6 : optimized 6 0 z18c6 = false := by decide +kernel

private def z18c7 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000, 0xdfdfdfdfdfdfdf0000000000ffff]
private theorem e7 : optimized 6 0 z18c7 = false := by decide +kernel

private def z18c8 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0xc0c0c0c0c0c0c0ffffff00000000, 0xdfdfdfdfdfdfdf0000000000ffff]
private theorem e8 : optimized 6 1 z18c8 = false := by decide +kernel

private def z18c9 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x3a3a3a3a3a3a3a00ff00ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e9 : optimized 6 0 z18c9 = false := by decide +kernel

private def z18c10 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x3c3c3c3c3c3c3cff0000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e10 : optimized 6 0 z18c10 = false := by decide +kernel

private def z18c11 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000, 0xe1e1e1e1e1e1e1ffffff00000000]
private theorem e11 : optimized 6 0 z18c11 = false := by decide +kernel

private def z18c12 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xe1e1e1e1e1e1e1ffffff00000000]
private theorem e12 : optimized 6 1 z18c12 = false := by decide +kernel

private def z18c13 : State := [0x202020202020200ff0000ff0000, 0x6060606060606ffff00ffff0000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e13 : optimized 6 0 z18c13 = false := by decide +kernel

private def z18c14 : State := [0x202020202020200ff0000ff0000, 0x212121212121210000ff00000000, 0x25252525252525ff00ffff000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e14 : optimized 6 0 z18c14 = false := by decide +kernel

private def z18c15 : State := [0x202020202020200ff0000ff0000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x3c3c3c3c3c3c3cff0000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e15 : optimized 6 0 z18c15 = false := by decide +kernel

private def z18c16 : State := [0x202020202020200ff0000ff0000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000, 0xc4c4c4c4c4c4c4ffffffff000000]
private theorem e16 : optimized 6 0 z18c16 = false := by decide +kernel

private def z18c17 : State := [0x202020202020200ff0000ff0000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc4c4c4c4c4c4c4ffffffff000000]
private theorem e17 : optimized 6 1 z18c17 = false := by decide +kernel

private def z18c18 : State := [0x202020202020200ff0000ff0000, 0x212121212121210000ff00000000, 0x3c3c3c3c3c3c3cff0000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e18 : optimized 6 1 z18c18 = false := by decide +kernel

private def z18c19 : State := [0x4040404040404ff0000ff000000, 0x6060606060606ffff00ffff0000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e19 : optimized 6 0 z18c19 = false := by decide +kernel

private def z18c20 : State := [0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x2323232323232300ffff00ff0000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e20 : optimized 6 0 z18c20 = false := by decide +kernel

private def z18c21 : State := [0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x3a3a3a3a3a3a3a00ff00ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e21 : optimized 6 0 z18c21 = false := by decide +kernel

private def z18c22 : State := [0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000, 0xc2c2c2c2c2c2c2ffffff00ff0000]
private theorem e22 : optimized 6 0 z18c22 = false := by decide +kernel

private def z18c23 : State := [0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc2c2c2c2c2c2c2ffffff00ff0000]
private theorem e23 : optimized 6 1 z18c23 = false := by decide +kernel

private def z18c24 : State := [0x4040404040404ff0000ff000000, 0x212121212121210000ff00000000, 0x3a3a3a3a3a3a3a00ff00ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e24 : optimized 6 1 z18c24 = false := by decide +kernel

private def z18c25 : State := [0x6060606060606ffff00ffff0000, 0x212121212121210000ff00000000, 0x38383838383838000000ffff0000, 0x4f4f4f4f4f4f4f0000000000ffff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
private theorem e25 : optimized 6 1 z18c25 = false := by decide +kernel

private def next : Layer := #[z18c0,z18c1,z18c2,z18c3,z18c4,z18c5,z18c6,z18c7,z18c8,z18c9,z18c10,z18c11,z18c12,z18c13,z18c14,z18c15,z18c16,z18c17,z18c18,z18c19,z18c20,z18c21,z18c22,z18c23,z18c24,z18c25]
private theorem afterStep : AtlasCut.Anchors 6 next := by
  intro s mem nd
  simp only [next, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
private theorem completeStep : (#[s18] : Layer).all (stateOK next 7) = true := by decide +kernel
theorem node18 : s18.Nodup → ¬ live basicOps goal 7 s18.toFinset :=
  (AtlasCut.step afterStep completeStep) s18 (by simp)

end CutWords3324
