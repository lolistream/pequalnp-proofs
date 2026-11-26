import SelectedOptima
import RepresentativeOrbitCoverage

namespace PEqualNP.Rep35Classification

open PEqualNP.Represents

/-- Lower-bound certificates can be replayed independently and then combined. -/
def LowerTable (xs : List (ℕ × ℕ)) : Prop := ∀ p ∈ xs, AtlasLower.lower p.1 p.2

def catalogue : List (ℕ × ℕ) := Rep35Upper.entries.map (fun e => (e.mask, e.budget))

theorem already_selected : LowerTable Rep35Selected.selected := by
  intro p hp t h
  exact (Rep35Selected.budget_iff hp t).1 h

theorem budget_of_lower {m k : ℕ} (hmem : (m, k) ∈ catalogue)
    (hl : AtlasLower.lower m k) (s : ℕ) :
    RepSizeAtMost (AtlasLower.graph m) s ↔ k ≤ s := by
  constructor
  · exact hl s
  · intro hs
    obtain ⟨e, he, eqn⟩ := List.mem_map.mp hmem
    have hm : e.mask = m := congrArg Prod.fst eqn
    have hk : e.budget = k := congrArg Prod.snd eqn
    have hu : RepSizeAtMost (AtlasLower.graph e.mask) e.budget := Rep35Upper.entries_upper e he
    rw [hm, hk] at hu
    obtain ⟨C, hop, hsize, hrep⟩ := hu
    exact ⟨C, hop, hsize.trans hs, hrep⟩

private theorem size_of_budget {A : Fin 3 → Fin 5 → Bool} {k : ℕ}
    (h : ∀ s, RepSizeAtMost A s ↔ k ≤ s) : repSize A = (k : ℕ∞) := by
  unfold repSize
  apply le_antisymm
  · exact sInf_le ⟨k, rfl, (h k).2 (by omega)⟩
  · apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    exact_mod_cast (h t).1 ht

/-- Minimum of any relabeling once the representative's lower proof is supplied. -/
theorem relabel_size_of_lower {m k : ℕ} (hmem : (m, k) ∈ catalogue)
    (hl : AtlasLower.lower m k) (r : Equiv.Perm (Fin 3)) (c : Equiv.Perm (Fin 5)) :
    repSize (fun u v => AtlasLower.graph m (r u) (c v)) = (k : ℕ∞) := by
  rw [repSize_perm]
  exact size_of_budget (budget_of_lower hmem hl)

set_option maxRecDepth 16000 in
private theorem mask_list : Rep35Upper.entries.map Rep35Upper.Entry.mask = Rep35Orbit.masks.toList := by
  decide +kernel

/-- A lower certificate for the finite catalogue implies a classification of arbitrary
labeled input relations, not just matrices occurring verbatim in that catalogue. -/
theorem classify_of_lower (hl : LowerTable catalogue) (A : Fin 3 → Fin 5 → Bool) :
    ∃ e ∈ Rep35Upper.entries, ∃ r : Equiv.Perm (Fin 3), ∃ c : Equiv.Perm (Fin 5),
      (∀ i j, A i j = AtlasLower.graph e.mask (r i) (c j)) ∧
      (∀ s, RepSizeAtMost A s ↔ e.budget ≤ s) ∧ repSize A = (e.budget : ℕ∞) := by
  obtain ⟨m, hm, r, c, h⟩ := Rep35Orbit.covers_all A
  rw [← mask_list] at hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  have p : (e.mask, e.budget) ∈ catalogue := List.mem_map.mpr ⟨e, he, rfl⟩
  have eqn : A = fun i j => AtlasLower.graph e.mask (r i) (c j) := funext (fun i => funext (h i))
  refine ⟨e, he, r, c, h, ?_, ?_⟩
  · intro s
    rw [eqn]
    exact (repSizeAtMost_perm_iff (AtlasLower.graph e.mask) s r c).trans (budget_of_lower p (hl _ p) s)
  · rw [eqn]
    exact relabel_size_of_lower p (hl _ p) r c

end PEqualNP.Rep35Classification
