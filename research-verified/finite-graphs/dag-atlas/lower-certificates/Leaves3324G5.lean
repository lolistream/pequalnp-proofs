import AtlasCut

namespace CutWords3324
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def s24 : State := [0x202020202020200ff0000ff0000, 0x70707070707070000000000ffff, 0x212121212121210000ff00000000, 0x3c3c3c3c3c3c3cff0000ffff0000, 0x48484848484848000000000000ff, 0x909090909090900000000000ff00, 0xc0c0c0c0c0c0c0ffffff00000000]
theorem t24 : optimized 7 1 s24 = false := by decide +kernel

end CutWords3324
