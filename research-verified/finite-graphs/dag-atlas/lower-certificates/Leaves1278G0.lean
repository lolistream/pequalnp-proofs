import AtlasCut

namespace CutWords1278
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def s13 : State := [0x404040404040400ff000000ff00, 0x8080808080808ff000000ff0000, 0xf0f0f0f0f0f0f000000000000ff, 0x21212121212121000000ff000000, 0x7070707070707000000000ffff00, 0x90909090909090000000000000ff, 0xc2c2c2c2c2c2c2ffffffff000000]
theorem t13 : optimized 7 1 s13 = false := by decide +kernel

end CutWords1278
