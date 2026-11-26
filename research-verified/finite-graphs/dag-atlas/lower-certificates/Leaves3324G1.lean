import AtlasCut

namespace CutWords3324
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def s14 : State := [0x202020202020200ff0000ff0000, 0x4040404040404ff0000ff000000, 0x70707070707070000000000ffff, 0x38383838383838000000ffff0000, 0x48484848484848000000000000ff, 0x909090909090900000000000ff00, 0xe1e1e1e1e1e1e1ffffff00000000]
theorem t14 : optimized 7 1 s14 = false := by decide +kernel

end CutWords3324
