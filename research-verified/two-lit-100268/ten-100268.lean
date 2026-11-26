import Mathlib
import PEqualNP.Defs

namespace TwoLit100268
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The ten-gate construction supplied with the unit, on its exact shared-wire promise. -/
theorem at_most_ten : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (100268 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[
    ⟨.or, [0,5]⟩, ⟨.not, [6]⟩, ⟨.and, [1,7]⟩,
    ⟨.or, [0,3]⟩, ⟨.or, [4,9]⟩, ⟨.and, [2,10]⟩,
    ⟨.or, [3,5]⟩, ⟨.and, [0,12]⟩, ⟨.or, [8,11]⟩, ⟨.or, [13,14]⟩], 15⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [FanInTwo, C]
  · decide +kernel

end TwoLit100268
