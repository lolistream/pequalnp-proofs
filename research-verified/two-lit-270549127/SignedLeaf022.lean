import Case24992

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC1088 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3fffffffffc000fffc000fffffff, 0x31dfc77f1dfc77f1dfc77f1dfc77)]
theorem qC1088 : Impossible 8 2 sC1088 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC0689 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3fffffffffffffc0000000000, 0x3fe3ff8ffe3ff8ffe3ff8ffe3ff8), (0x3ffc0000003fff0003ffffffffff, 0xe3c38f0e3c38f0e3c38f0e3c38f)]
theorem qC0689 : Impossible 7 1 sC0689 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower24992
