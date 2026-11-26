import Mathlib
import PEqualNP.Defs

namespace Fin5Mask24608768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [11, 9]⟩,
    ⟨.and, [3, 12]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [14, 15]⟩], 16⟩

theorem upper_seven :
    RepSizeAtMost (fun u v : Fin 5 => (24608768 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel

end Fin5Mask24608768
