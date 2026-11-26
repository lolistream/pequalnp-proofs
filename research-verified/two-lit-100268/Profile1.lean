import Ob0000
import Ob0001
import Ob0002
import Ob0003
import Ob0004
import Ob0005
import Ob0006
import Ob0007
import Ob0008
import Ob0009
import Ob0010
import Ob0011
import Ob0012
import Ob0013
import Ob0014
import Ob0015
import Ob0016
import Ob0017
import Ob0018
import Ob0019
import Ob0020
import Ob0021
import Ob0022
import Ob0023
import Ob0024
import Ob0025
import Ob0026
import Ob0027
import Ob0028
import Ob0029
import Ob0030
import Ob0031
import Ob0032
import Ob0033
import Ob0034
import Ob0035
import Ob0036
import Ob0037
import Ob0038
import Ob0039
import Ob0040
import Ob0041
import Ob0042
import Ob0043
import Ob0044
import Ob0045
import SignedSearch

namespace Lower100268
open TwoLit100268
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

private def us1 : List (List Sig) := []
private def bs1 : List (List Sig) := [sOb0000, sOb0001, sOb0002, sOb0003, sOb0004, sOb0005, sOb0006, sOb0007, sOb0008, sOb0009, sOb0010, sOb0011, sOb0012, sOb0013, sOb0014, sOb0015, sOb0016, sOb0017, sOb0018, sOb0019, sOb0020, sOb0021, sOb0022, sOb0023, sOb0024, sOb0025, sOb0026, sOb0027, sOb0028, sOb0029, sOb0030, sOb0031, sOb0032, sOb0033, sOb0034, sOb0035, sOb0036, sOb0037, sOb0038, sOb0039, sOb0040, sOb0041, sOb0042, sOb0043, sOb0044, sOb0045]
theorem profile1 : Impossible 9 1 raw := by
  apply cut (us := us1) (bs := bs1) raw_nodup_public
  · decide +kernel
  · simp [us1]
  · intro x hx
    simp only [bs1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qOb0000
    · exact qOb0001
    · exact qOb0002
    · exact qOb0003
    · exact qOb0004
    · exact qOb0005
    · exact qOb0006
    · exact qOb0007
    · exact qOb0008
    · exact qOb0009
    · exact qOb0010
    · exact qOb0011
    · exact qOb0012
    · exact qOb0013
    · exact qOb0014
    · exact qOb0015
    · exact qOb0016
    · exact qOb0017
    · exact qOb0018
    · exact qOb0019
    · exact qOb0020
    · exact qOb0021
    · exact qOb0022
    · exact qOb0023
    · exact qOb0024
    · exact qOb0025
    · exact qOb0026
    · exact qOb0027
    · exact qOb0028
    · exact qOb0029
    · exact qOb0030
    · exact qOb0031
    · exact qOb0032
    · exact qOb0033
    · exact qOb0034
    · exact qOb0035
    · exact qOb0036
    · exact qOb0037
    · exact qOb0038
    · exact qOb0039
    · exact qOb0040
    · exact qOb0041
    · exact qOb0042
    · exact qOb0043
    · exact qOb0044
    · exact qOb0045
end Lower100268
