import MemoLower

namespace MemoRow35
open AtlasLower AtlasMemo

def cols : List W := [0xdb6db6db6db6db001ff0000001ff,0x24924924924924ffe000001ffe00,0xfffe00000,0x6db6db6db6db6d00000000e00000,0x9249249249249200e00007000e00,0x7007038007007,0x380381c0038038,0xc01c0e001c01c0]
set_option maxRecDepth 12000 in
def layer0 : Layer := #[]
set_option maxRecDepth 12000 in
def layer1 : Layer := #[]
set_option maxRecDepth 12000 in
def layer2 : Layer := #[[0x6db6db6db6db6d00000000e00000,0xb6db6db6db6db6ffe000071ffe00,0xdb6db6db6db6db001ff0000001ff]]
set_option maxRecDepth 12000 in
def layer3 : Layer := #[[0x24924924924924ffe000001ffe00,0x6db6db6db6db6d00000000e00000,0x9249249249249200e00007000e00,0xdb6db6db6db6db001ff0000001ff]]
def cert : Table := #[layer0,layer1,layer2,layer3]
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 15000 in
theorem result : AtlasLower.lower 35 4 :=
  AtlasMemo.sound (samp := sample 35) (xs := cols) cert
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end MemoRow35
