import AtlasCut

namespace CutWords1150
open AtlasLower AtlasMemo
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

def s14 : State := [0x40810204081020003f800003f80, 0x810204081020401fc00001fc000, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
theorem t14 : optimized 7 1 s14 = false := by decide +kernel

end CutWords1150
