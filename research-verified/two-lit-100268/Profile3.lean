import Ob0104
import Ob0105
import Ob0106
import Ob0107
import Ob0108
import Ob0109
import Ob0110
import Ob0111
import Ob0112
import Ob0113
import Ob0114
import Ob0115
import Ob0116
import Ob0117
import Ob0118
import Ob0119
import Ob0120
import Ob0121
import Ob0122
import Ob0123
import Ob0124
import Ob0125
import Ob0126
import Ob0127
import Ob0128
import Ob0129
import Ob0130
import Ob0131
import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

private def us3 : List (List Sig) := [sOb0104, sOb0105, sOb0106, sOb0107, sOb0108, sOb0109, sOb0110, sOb0111, sOb0112, sOb0113, sOb0114, sOb0115]
private def bs3 : List (List Sig) := [sOb0116, sOb0117, sOb0118, sOb0119, sOb0120, sOb0121, sOb0122, sOb0123, sOb0124, sOb0125, sOb0126, sOb0127, sOb0128, sOb0129, sOb0130, sOb0131]
theorem profile3 : Impossible 9 3 raw := by
  apply cut (us := us3) (bs := bs3) raw_nodup_public
  · decide +kernel
  · intro x hx
    simp only [us3, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qOb0104
    · exact qOb0105
    · exact qOb0106
    · exact qOb0107
    · exact qOb0108
    · exact qOb0109
    · exact qOb0110
    · exact qOb0111
    · exact qOb0112
    · exact qOb0113
    · exact qOb0114
    · exact qOb0115
  · intro x hx
    simp only [bs3, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qOb0116
    · exact qOb0117
    · exact qOb0118
    · exact qOb0119
    · exact qOb0120
    · exact qOb0121
    · exact qOb0122
    · exact qOb0123
    · exact qOb0124
    · exact qOb0125
    · exact qOb0126
    · exact qOb0127
    · exact qOb0128
    · exact qOb0129
    · exact qOb0130
    · exact qOb0131
end Lower100268
