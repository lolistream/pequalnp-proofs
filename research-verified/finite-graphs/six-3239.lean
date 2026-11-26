import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem upper_L_meta_20498 : PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 3) (v : Fin 5) => (3239 : ℕ).testBit (5 * u.val + v.val)) 6 := by
  let C : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [0, 1]⟩,
    ⟨.and, [5, 10]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [Monotone2, C]
  · decide +kernel
