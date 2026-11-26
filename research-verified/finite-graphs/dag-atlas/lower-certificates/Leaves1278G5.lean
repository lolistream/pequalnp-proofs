import AtlasCut

namespace CutWords1278
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def s26 : State := [0x404040404040400ff000000ff00, 0xf0f0f0f0f0f0f000000000000ff, 0x21212121212121000000ff000000, 0x424242424242420000ff00000000, 0x78787878787878ff000000ffff00, 0x80808080808080ffffffff000000, 0x90909090909090000000000000ff]
theorem t26 : optimized 7 1 s26 = false := by decide +kernel

end CutWords1278
