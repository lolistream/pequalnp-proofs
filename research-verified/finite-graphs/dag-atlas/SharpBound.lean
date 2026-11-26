import RepSizePerm
import RepresentativeOrbitCoverage
import RepresentativeUpperBounds
import WorstCase

namespace PEqualNP.Rep35Atlas

open PEqualNP.Represents

set_option maxRecDepth 10000 in
private theorem sameMasks : Rep35Upper.entries.map Rep35Upper.Entry.mask = Rep35Orbit.masks.toList := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem budgets : Rep35Upper.entries.all (fun e => decide (e.budget ≤ 9)) = true := by
  decide +kernel

/-- Every labeled relation between three row vertices and five column vertices
has a monotone circuit with at most nine gates under the one-hot promise. -/
theorem all_at_most_nine (A : Fin 3 → Fin 5 → Bool) : RepSizeAtMost A 9 := by
  obtain ⟨m, hm, r, p, h⟩ := Rep35Orbit.covers_all A
  rw [← sameMasks] at hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  have hb : e.budget ≤ 9 := of_decide_eq_true ((List.all_eq_true.mp budgets) e he)
  obtain ⟨C, hop, hsize, hrep⟩ := Rep35Upper.entries_upper e he
  have hbound : RepSizeAtMost (Rep35Upper.adjacency e.mask) 9 := ⟨C, hop, hsize.trans hb, hrep⟩
  have eqn : A = fun i j => Rep35Upper.adjacency e.mask (r i) (p j) :=
    funext (fun i => funext (h i))
  rw [eqn]
  exact (repSizeAtMost_perm_iff _ _ r p).2 hbound

/-- Nine is the least uniform gate budget: this statement includes both the
universal upper bound and an obstructing relation for every smaller budget. -/
theorem sharp_uniform_bound (s : ℕ) :
    (∀ A : Fin 3 → Fin 5 → Bool, RepSizeAtMost A s) ↔ 9 ≤ s := by
  constructor
  · intro h
    by_contra hn
    have h8 : s ≤ 8 := by omega
    obtain ⟨C, hop, hsize, hrep⟩ := h (Rep35Upper.adjacency 7549)
    exact refute_MatrixRefutation3x5Mask7549Budget8 ⟨C, hop, hsize.trans h8, hrep⟩
  · intro hs A
    obtain ⟨C, hop, hsize, hrep⟩ := all_at_most_nine A
    exact ⟨C, hop, hsize.trans hs, hrep⟩

end PEqualNP.Rep35Atlas
