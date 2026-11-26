import AtlasCut

namespace CutWords1278
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def s33 : State := [0x8080808080808ff000000ff0000, 0xf0f0f0f0f0f0f000000000000ff, 0x21212121212121000000ff000000, 0x424242424242420000ff00000000, 0x7474747474747400ff0000ffff00, 0x80808080808080ffffffff000000, 0x90909090909090000000000000ff]
theorem t33 : optimized 7 1 s33 = false := by decide +kernel

end CutWords1278
