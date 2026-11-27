import Case24992

namespace Lower24992
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 8500000

def sC1016 : List Sig := [(0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0x2f33bccef33bccef33bccef33bcc), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
theorem qC1016 : Impossible 7 2 sC1016 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC1017 : List Sig := [(0xfffc000fffc000, 0x29f3a7ce9f3a7ce9f3a7ce9f3a7c), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x3d9bf66fd9bf66fd9bf66fd9bf66), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
theorem qC1017 : Impossible 7 2 sC1017 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC1031 : List Sig := [(0xfffc000fffc000, 0x1e007801e007801e007801e0078), (0x3fff0003fff0000000, 0x2f33bccef33bccef33bccef33bcc), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
theorem qC1031 : Impossible 7 2 sC1031 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC1032 : List Sig := [(0xfffc000fffc000, 0x29f3a7ce9f3a7ce9f3a7ce9f3a7c), (0x3fff0003fff0000000, 0xe203880e203880e203880e20388), (0xfffc00000000000000000, 0x3b57ed5fb57ed5fb57ed5fb57ed5), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007)]
theorem qC1032 : Impossible 7 2 sC1032 :=
  exclude_search (by decide +kernel) (by decide +kernel)

def sC0860 : List Sig := [(0x0, 0x2913a44e913a44e913a44e913a44), (0xfffc000fffc000, 0x29f3a7ce9f3a7ce9f3a7ce9f3a7c), (0xfffc00000000000000000, 0x3244c913244c913244c913244c91), (0x3fff000000000000000000000, 0x1489522548952254895225489522), (0x3ffc00000000000003ffffffffff, 0x1c007001c007001c007001c007), (0x3fffffffffc000fffc000fffffff, 0x31dfc77f1dfc77f1dfc77f1dfc77)]
theorem qC0860 : Impossible 7 1 sC0860 :=
  exclude_search (by decide +kernel) (by decide +kernel)

end Lower24992
