import PEqualNP.Outside.L_meta_10135
import NewHigh11

namespace Graph4x5Mask111351
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def graph (u : Fin 4) (v : Fin 5) := (111351 : ℕ).testBit (5 * u.val + v.val)

/-- Deleting the first of two identical rows yields mask 3479, but also removes a gate:
row 0 distinguishes (0,0) from (2,0), and it cannot itself be the output, by (0,3). -/
theorem no_nine : ¬ RepSizeAtMost graph 9 := by
  intro h
  have small : RepSizeAtMost (AtlasLower.graph 3479) 8 :=
    PEqualNP.Outside.L_meta_10135.smaller (k := 8) 111351 3479
      (Fin.succ : Fin 3 → Fin 4) (id : Fin 5 → Fin 5) 0
      (0,0) (2,0) (0,3) (by decide +kernel) h
  exact (by decide : ¬ (9 : ℕ) ≤ 8) (NewHigh11.row3479 8 small)

/-- The gates are listed in order after the four row wires and five column wires. -/
theorem at_most_ten : RepSizeAtMost graph 10 := by
  let C : Circuit := ⟨[
    ⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.or, [3,6]⟩, ⟨.or, [5,10]⟩,
    ⟨.or, [7,9]⟩, ⟨.or, [8,11]⟩, ⟨.and, [9,14]⟩, ⟨.or, [11,13]⟩,
    ⟨.or, [12,15]⟩, ⟨.and, [16,17]⟩], 18⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [Monotone2, C]
  · decide +kernel

/-- The exact budget for the one-hot relation posed in L-meta-21080. -/
theorem exact_budget (s : ℕ) : RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 5) => (111351 : ℕ).testBit (5 * u.val + v.val)) s ↔ 10 ≤ s := by
  constructor
  · rintro ⟨C, hm, hs, hrep⟩
    by_contra hn
    exact no_nine ⟨C, hm, hs.trans (show s ≤ 9 by omega), hrep⟩
  · intro hs
    obtain ⟨C, hm, hsize, hrep⟩ := at_most_ten
    exact ⟨C, hm, hsize.trans hs, hrep⟩

end Graph4x5Mask111351
