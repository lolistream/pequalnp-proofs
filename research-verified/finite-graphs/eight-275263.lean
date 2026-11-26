import Mathlib
import PEqualNP.Defs

namespace Graph4x6Mask275263
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Row 0 is full. The other rows accept columns {2,3}, {0,1} and {0}, respectively. -/
theorem at_most_eight : RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 6) => (275263 : ℕ).testBit (6 * u.val + v.val)) 8 := by
  let C : Circuit := ⟨[
    ⟨.or, [6, 7]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [2, 12]⟩,
    ⟨.and, [3, 4]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [15, 16]⟩], 17⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [Monotone2, C]
  · decide +kernel

end Graph4x6Mask275263
