import Ob0046
import Ob0047
import Ob0048
import Ob0049
import Ob0050
import Ob0051
import Ob0052
import Ob0053
import Ob0054
import Ob0055
import Ob0056
import Ob0057
import Ob0058
import Ob0059
import Ob0060
import Ob0061
import Ob0062
import Ob0063
import Ob0064
import Ob0065
import Ob0066
import Ob0067
import Ob0068
import Ob0069
import Ob0070
import Ob0071
import Ob0072
import Ob0073
import Ob0074
import Ob0075
import Ob0076
import Ob0077
import Ob0078
import Ob0079
import Ob0080
import Ob0081
import Ob0082
import Ob0083
import Ob0084
import Ob0085
import Ob0086
import Ob0087
import Ob0088
import Ob0089
import Ob0090
import Ob0091
import Ob0092
import Ob0093
import Ob0094
import Ob0095
import Ob0096
import Ob0097
import Ob0098
import Ob0099
import Ob0100
import Ob0101
import Ob0102
import Ob0103
import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

private def us2 : List (List Sig) := [sOb0046, sOb0047, sOb0048, sOb0049, sOb0050, sOb0051, sOb0052, sOb0053, sOb0054, sOb0055, sOb0056, sOb0057]
private def bs2 : List (List Sig) := [sOb0058, sOb0059, sOb0060, sOb0061, sOb0062, sOb0063, sOb0064, sOb0065, sOb0066, sOb0067, sOb0068, sOb0069, sOb0070, sOb0071, sOb0072, sOb0073, sOb0074, sOb0075, sOb0076, sOb0077, sOb0078, sOb0079, sOb0080, sOb0081, sOb0082, sOb0083, sOb0084, sOb0085, sOb0086, sOb0087, sOb0088, sOb0089, sOb0090, sOb0091, sOb0092, sOb0093, sOb0094, sOb0095, sOb0096, sOb0097, sOb0098, sOb0099, sOb0100, sOb0101, sOb0102, sOb0103]
theorem profile2 : Impossible 9 2 raw := by
  apply cut (us := us2) (bs := bs2) raw_nodup_public
  · decide +kernel
  · intro x hx
    simp only [us2, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qOb0046
    · exact qOb0047
    · exact qOb0048
    · exact qOb0049
    · exact qOb0050
    · exact qOb0051
    · exact qOb0052
    · exact qOb0053
    · exact qOb0054
    · exact qOb0055
    · exact qOb0056
    · exact qOb0057
  · intro x hx
    simp only [bs2, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qOb0058
    · exact qOb0059
    · exact qOb0060
    · exact qOb0061
    · exact qOb0062
    · exact qOb0063
    · exact qOb0064
    · exact qOb0065
    · exact qOb0066
    · exact qOb0067
    · exact qOb0068
    · exact qOb0069
    · exact qOb0070
    · exact qOb0071
    · exact qOb0072
    · exact qOb0073
    · exact qOb0074
    · exact qOb0075
    · exact qOb0076
    · exact qOb0077
    · exact qOb0078
    · exact qOb0079
    · exact qOb0080
    · exact qOb0081
    · exact qOb0082
    · exact qOb0083
    · exact qOb0084
    · exact qOb0085
    · exact qOb0086
    · exact qOb0087
    · exact qOb0088
    · exact qOb0089
    · exact qOb0090
    · exact qOb0091
    · exact qOb0092
    · exact qOb0093
    · exact qOb0094
    · exact qOb0095
    · exact qOb0096
    · exact qOb0097
    · exact qOb0098
    · exact qOb0099
    · exact qOb0100
    · exact qOb0101
    · exact qOb0102
    · exact qOb0103
end Lower100268
