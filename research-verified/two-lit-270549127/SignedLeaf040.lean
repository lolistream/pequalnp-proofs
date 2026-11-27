import Case24992

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0260 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc0000003fffffffffffffffff, 0xffc3ff0ffc3ff0ffc3ff0ffc3ff)]
theorem qC0260 : Impossible 7 1 sC0260 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC0491 : List Sig := [(0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0x2f33bccef33bccef33bccef33bcc), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
theorem qC0491 : Impossible 7 1 sC0491 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower24992
