import Mathlib
import PEqualNP.Defs

namespace Graph4x5Mask106399
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- Row 0 is full. Rows 2 and 3 reuse the signal for columns 0 or 1.
theorem at_most_ten : RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 5) => (106399 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  let C : Circuit := ⟨[
    ⟨.or, [4,5]⟩, ⟨.or, [7,8]⟩, ⟨.or, [6,10]⟩, ⟨.or, [9,6]⟩,
    ⟨.and, [1,11]⟩, ⟨.and, [2,12]⟩, ⟨.and, [3,9]⟩,
    ⟨.or, [0,13]⟩, ⟨.or, [16,14]⟩, ⟨.or, [17,15]⟩], 18⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [Monotone2, C]
  · decide +kernel

end Graph4x5Mask106399
