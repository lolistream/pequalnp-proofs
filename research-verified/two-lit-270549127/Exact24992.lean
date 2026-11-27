import SignedCut0001
import SignedCut0619
import SignedCut1078
import LastInverterCase
import Ten24992

namespace SixPoint270549127
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The four possible normalized NOT counts are all excluded for this mask and budget. -/
theorem no_nine : ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (270549127 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  Case24992.no_nine_of_profiles Lower24992.qC0001 Lower24992.qC0619
    Lower24992.qC1078 Case24992.four_impossible

/-- Exact minimum for L-meta-24992, on the shared six wires, including the cases i = j. -/
theorem exact_budget (s : ℕ) :
    (∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ ∀ i j : Fin 6,
      C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (270549127 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) ↔ 10 ≤ s := by
  constructor
  · rintro ⟨C, hfan, hsize, heval⟩
    by_contra h
    exact no_nine ⟨C, hfan, hsize.trans (show s ≤ 9 by omega), heval⟩
  · intro h
    obtain ⟨C, hfan, hsize, heval⟩ := at_most_ten
    exact ⟨C, hfan, hsize.trans h, heval⟩

end SixPoint270549127
