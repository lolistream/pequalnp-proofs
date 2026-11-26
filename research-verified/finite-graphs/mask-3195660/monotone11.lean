import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem MonotoneMatrix19528Size11 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3195660 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  let C : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [10, 15]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [4, 17]⟩, ⟨.and, [14, 18]⟩, ⟨.or, [12, 19]⟩], 20⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [Monotone2, C]
  · decide +kernel
