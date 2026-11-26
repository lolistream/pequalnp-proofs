import Mathlib
import PEqualNP.Defs

namespace Matrix53
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- r₀ ∧ (c₀ ∨ c₂), or r₁ ∧ (c₀ ∨ c₁).
private def rowStars : Circuit :=
  ⟨[⟨.or, [3, 5]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 9]⟩,
    ⟨.or, [8, 10]⟩], 11⟩

private theorem size_at_most_five : RepSizeAtMost
    (fun (u : Fin 3) (v : Fin 4) => (53 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  refine ⟨rowStars, ?_, by decide, by decide⟩
  intro g hg
  simp [rowStars] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end Matrix53
