import Case24992

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC0237 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0x2f33bccef33bccef33bccef33bcc), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc0000003fff0003ffffffffff, 0xe3c38f0e3c38f0e3c38f0e3c38f)]
theorem qC0237 : Impossible 7 1 sC0237 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC0968 : List Sig := [(0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x291fa47e91fa47e91fa47e91fa47)]
theorem qC0968 : Impossible 7 2 sC0968 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC0969 : List Sig := [(0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x291fa47e91fa47e91fa47e91fa47)]
theorem qC0969 : Impossible 7 2 sC0969 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC1015 : List Sig := [(0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
theorem qC1015 : Impossible 7 2 sC1015 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC0817 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3ffffff0003fffffffffffffffff, 0xdbb36ecdbb36ecdbb36ecdbb36e)]
theorem qC0817 : Impossible 7 1 sC0817 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower24992
