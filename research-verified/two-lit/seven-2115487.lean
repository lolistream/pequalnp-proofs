import Mathlib
import PEqualNP.Defs

namespace TwoLit2115487
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- This circuit realizes the desk's mask on both the singleton and the two-point inputs. -/
theorem at_most_seven : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2115487 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.not, [6]⟩, ⟨.and, [4, 7]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [5, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [FanInTwo, C]
  · decide +kernel

end TwoLit2115487
