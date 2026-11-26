import AtlasCut

namespace CutWords1278
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def s25 : State := [0x404040404040400ff000000ff00, 0xf0f0f0f0f0f0f000000000000ff, 0x21212121212121000000ff000000, 0x424242424242420000ff00000000, 0x7070707070707000000000ffff00, 0x88888888888888ffffffffff0000, 0x90909090909090000000000000ff]
theorem t25 : optimized 7 1 s25 = false := by decide +kernel

end CutWords1278
