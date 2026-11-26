import Mathlib
import PEqualNP.Defs

namespace TwoLit35895
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem at_most_seven : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (35895 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.not, [3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 8]⟩,
    ⟨.and, [2, 3]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [10, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [FanInTwo, C]
  · decide +kernel

end TwoLit35895
