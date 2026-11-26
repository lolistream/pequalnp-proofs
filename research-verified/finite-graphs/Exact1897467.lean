import PEqualNP.Outside.L_meta_10135
import NewHigh14

namespace Graph4x6Mask1897467
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_10135 (smaller)

private def graph (u : Fin 4) (v : Fin 6) : Bool := (1897467 : ℕ).testBit (6 * u.val + v.val)

/-- Delete row 1 and then column 5. Each deletion saves a gate, since two
promise inputs can only be separated by the deleted wire. The remaining
3 by 5 submatrix is mask 7675, whose certified minimum is nine. -/
theorem no_ten : ¬ RepSizeAtMost graph 10 := by
  intro h
  have h₁ := smaller (k := 9) 1897467 29691
    ((1 : Fin 4).succAbove : Fin 3 → Fin 4) (id : Fin 6 → Fin 6)
    1 (1,3) (3,3) (1,4) (by decide +kernel) h
  have h₂ := smaller (k := 8) 29691 7675
    (id : Fin 3 → Fin 3) (Fin.castSucc : Fin 5 → Fin 6)
    8 (0,5) (0,2) (1,5) (by decide +kernel) h₁
  exact (by decide : ¬ (9 : ℕ) ≤ 8) (NewHigh14.row7675 8 h₂)

/-- First gate at wire 10, output at wire 20. -/
theorem at_most_eleven : RepSizeAtMost graph 11 := by
  let C : Circuit := ⟨[
    ⟨.or, [0,6]⟩, ⟨.or, [1,2]⟩, ⟨.or, [3,7]⟩, ⟨.or, [4,5]⟩,
    ⟨.or, [8,9]⟩, ⟨.or, [10,11]⟩, ⟨.or, [11,14]⟩, ⟨.and, [10,16]⟩,
    ⟨.and, [12,15]⟩, ⟨.or, [13,17]⟩, ⟨.or, [18,19]⟩], 20⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [Monotone2, C]
  · decide +kernel

/-- Exact AND/OR gate budget of the one-hot relation posed by L-meta-23489. -/
theorem exact_budget (s : ℕ) : RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 6) => (1897467 : ℕ).testBit (6 * u.val + v.val)) s ↔ 11 ≤ s := by
  constructor
  · rintro ⟨C, hm, hs, he⟩
    by_contra hn
    exact no_ten ⟨C, hm, hs.trans (show s ≤ 10 by omega), he⟩
  · intro hs
    obtain ⟨C, hm, hsize, he⟩ := at_most_eleven
    exact ⟨C, hm, hsize.trans hs, he⟩

end Graph4x6Mask1897467
