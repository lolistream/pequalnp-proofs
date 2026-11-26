import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def alt20463c5 : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [10, 4]⟩,
    ⟨.or, [9, 11]⟩], 12⟩

private theorem alt20463_size_five : RepSizeAtMost
    (fun (u : Fin 3) (v : Fin 5) => (1091 : ℕ).testBit (5 * u.val + v.val)) 5 := by
  refine ⟨alt20463c5, ?_, by decide, by decide⟩
  intro g hg
  simp [alt20463c5] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside
