import AtlasCut

namespace CutWords3324
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def s30 : State := [0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x3a3a3a3a3a3a3a00ff00ffff0000, 0x48484848484848000000000000ff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
theorem t30 : optimized 7 1 s30 = false := by decide +kernel

end CutWords3324
