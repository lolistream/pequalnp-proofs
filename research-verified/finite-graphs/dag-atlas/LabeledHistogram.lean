import ExactClassification
import HistogramCounting
import HistogramFixers

namespace PEqualNP.Rep35Histogram

open PEqualNP.Represents PEqualNP.Rep35Classification

private abbrev WeightRow := ℕ × ℕ × ℕ
private def key (t : WeightRow) : ℕ × ℕ := (t.1, t.2.1)

/-- Number of *labeled* one-hot 3×5 relations whose least monotone circuit size is `k`. -/
noncomputable def labeledCount (k : ℕ) : ℕ := Nat.card {A : Matrix // repSize A = (k : ℕ∞)}

private def byWeight (k : ℕ) : ℕ :=
  (weights.map (fun t => if t.2.1 = k then t.2.2 else 0)).sum

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4500000 in
private theorem tables_agree : (∀ p ∈ catalogue, p ∈ weights.map key) ∧
    (∀ t ∈ weights, key t ∈ catalogue) := by decide +kernel

private noncomputable def piece (t : WeightRow) : Finset Matrix := orbit (AtlasLower.graph t.1)

private theorem cover (A : Matrix) : ∃ t ∈ weights, A ∈ piece t := by
  obtain ⟨e, he, r, c, eqn, _, _⟩ := exact_classification A
  have p : (e.mask, e.budget) ∈ catalogue := List.mem_map.mpr ⟨e, he, rfl⟩
  obtain ⟨t, ht, hkey⟩ := List.mem_map.mp (tables_agree.1 _ p)
  have hm : t.1 = e.mask := congrArg Prod.fst hkey
  refine ⟨t, ht, ?_⟩
  change A ∈ orbit (AtlasLower.graph t.1)
  rw [hm, mem_orbit_iff]
  exact ⟨(r, c), funext (fun i => funext (eqn i))⟩

private theorem piece_size (t : WeightRow) (ht : t ∈ weights) (A : Matrix) (hA : A ∈ piece t) :
    repSize A = (t.2.1 : ℕ∞) := by
  have h : (t.1, t.2.1) ∈ catalogue := tables_agree.2 t ht
  obtain ⟨g, rfl⟩ := (mem_orbit_iff A (AtlasLower.graph t.1)).1 hA
  exact relabel_size_of_lower h (all_lower _ h) g.1 g.2

set_option maxRecDepth 18000 in
private theorem total : (weights.map (fun t => t.2.2)).sum = Fintype.card Matrix := by
  rw [show Fintype.card Matrix = 32768 by simp [Matrix]]
  decide +kernel

/-- The minima are those of `repSize`, not of tree formulas or an input list of proposed costs. -/
theorem count_by_orbit_weights (k : ℕ) : labeledCount k = byWeight k :=
  count_eq_weight weights (fun A : Matrix => repSize A) (fun t => t.2.1) (fun t => t.2.2)
    piece cover piece_size weights_bound total k

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4500000 in
/-- The entry at index `k` counts all labeled 3×5 relations of exact minimum `k`. -/
theorem exact_histogram : (List.range 10).map labeledCount =
    [9, 44, 190, 605, 1500, 3180, 5460, 6150, 7860, 7770] := by
  calc
    _ = (List.range 10).map byWeight := List.map_congr_left (fun k _ => count_by_orbit_weights k)
    _ = _ := by decide +kernel

set_option maxRecDepth 18000 in
private theorem max_budget : ∀ t ∈ weights, t.2.1 ≤ 9 := by decide +kernel

theorem count_above_nine (k : ℕ) (hk : 9 < k) : labeledCount k = 0 := by
  rw [count_by_orbit_weights, byWeight]
  have h : weights.map (fun t => if t.2.1 = k then t.2.2 else 0) = weights.map (fun _ => (0 : ℕ)) := by
    apply List.map_congr_left
    intro t ht
    have hne : t.2.1 ≠ k := by have := max_budget t ht; omega
    simp [hne]
  rw [h]
  simp

set_option maxRecDepth 18000 in
/-- Exactly 7,770 *different labeled Boolean relations* require the ninth gate. -/
theorem exactly_nine : Nat.card {A : Fin 3 → Fin 5 → Bool // repSize A = 9} = 7770 := by
  change labeledCount 9 = _
  rw [count_by_orbit_weights]
  decide +kernel

end PEqualNP.Rep35Histogram
