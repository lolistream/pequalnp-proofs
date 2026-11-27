import Case24992

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0410 : List Sig := [(0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x291fa47e91fa47e91fa47e91fa47)]
theorem qC0410 : Impossible 7 1 sC0410 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC0411 : List Sig := [(0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x291fa47e91fa47e91fa47e91fa47)]
theorem qC0411 : Impossible 7 1 sC0411 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC0777 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffc000fffffffffffffffffffff, 0x2b76addab76addab76addab76add)]
theorem qC0777 : Impossible 7 1 sC0777 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower24992
