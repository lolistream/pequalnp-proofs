import SignedSearch
import Profile1
import Profile2
import Profile3

namespace TwoLit100268

/-- The signed live-wire catalogue rules out every circuit of at most nine gates
on the full two-point promise, including shared wires and NOT gates. -/
theorem no_nine : ¬ has 9 :=
  root_of_impossible (fun t lo hi => by
    interval_cases t
    · exact Lower100268.profile1
    · exact Lower100268.profile2
    · exact Lower100268.profile3
    · exact impossible_four)

end TwoLit100268
