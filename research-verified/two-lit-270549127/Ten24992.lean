import Mathlib
import PEqualNP.Defs

namespace SixPoint270549127
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The desk's ten-gate witness. The last NOT complements the union of all rejected cases. -/
theorem at_most_ten : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6,
    C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (270549127 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[
    ⟨.or, [0, 1]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [4, 7]⟩,
    ⟨.and, [1, 2]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 13]⟩,
    ⟨.not, [14]⟩], 15⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [FanInTwo, C]
  · decide +kernel

end SixPoint270549127
