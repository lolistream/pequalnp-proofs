import AtlasCut

namespace CutWords1150
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def s22 : State := [0x40810204081020003f800003f80, 0x810204081020401fc00001fc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x91224489122448ffffffffe00000, 0xa142850a1428500000000000007f]
theorem t22 : optimized 7 1 s22 = false := by decide +kernel

end CutWords1150
