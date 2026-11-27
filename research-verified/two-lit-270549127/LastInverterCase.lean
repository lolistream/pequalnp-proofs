import Case24992

namespace Case24992
open TwoLit100268

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
/-- At four normalized NOTs, no live operand can be reused under the nine-gate budget. -/
theorem four_impossible : Impossible 9 4 xs :=
  exclude_search xs_nodup (by decide +kernel)

end Case24992
