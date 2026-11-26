import Mathlib

namespace Geometry8752

abbrev Point := Fin 13
abbrev incident (i j : Point) : Prop := (i.val + j.val) % 13 ∈ [0, 1, 3, 9]

def avoid (S : Finset Point) : Finset Point :=
  Finset.univ.filter fun j => ∀ i ∈ S, ¬ incident i j

-- Each of the four rows contains four points; any pair meets in exactly one.
private theorem row_size : ∀ i : Point, (Finset.univ.filter fun j : Point => incident i j).card = 4 := by
  decide

private theorem rows_meet : ∀ i k : Point, i ≠ k →
    (Finset.univ.filter fun j : Point => incident i j ∧ incident k j).card = 1 := by
  decide

theorem avoid_four_le_three (A : Finset Point) (hA : A.card = 4) : (avoid A).card ≤ 3 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp hA
  let L := fun i : Point => Finset.univ.filter fun j : Point => incident i j
  have hpair (i k : Point) (hik : i ≠ k) : (L i ∩ L k).card = 1 := by
    have e : L i ∩ L k = Finset.univ.filter fun j : Point => incident i j ∧ incident k j := by
      ext j; simp [L]
    rw [e]; exact rows_meet i k hik
  have habc : ((L a ∪ L b) ∩ L c).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    exact (Finset.card_union_le _ _).trans (by rw [hpair a c hac, hpair b c hbc])
  have habcd : (((L a ∪ L b) ∪ L c) ∩ L d).card ≤ 3 := by
    simp only [Finset.union_inter_distrib_right]
    have h := Finset.card_union_le (L a ∩ L d) (L b ∩ L d)
    have k := Finset.card_union_le ((L a ∩ L d) ∪ (L b ∩ L d)) (L c ∩ L d)
    rw [hpair a d had, hpair b d hbd] at h
    rw [hpair c d hcd] at k
    omega
  have h1 := Finset.card_union_add_card_inter (L a) (L b)
  have h2 := Finset.card_union_add_card_inter (L a ∪ L b) (L c)
  have h3 := Finset.card_union_add_card_inter ((L a ∪ L b) ∪ L c) (L d)
  have ha : (L a).card = 4 := row_size a
  have hb : (L b).card = 4 := row_size b
  have hc : (L c).card = 4 := row_size c
  have hd : (L d).card = 4 := row_size d
  have h4 : (avoid {a,b,c,d}) = Finset.univ \ (((L a ∪ L b) ∪ L c) ∪ L d) := by
    ext j; simp [avoid, L]
  rw [h4, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hp := hpair a b hab
  omega

theorem incidence_free_min_le_three (S T : Finset Point)
    (h : ∀ i ∈ S, ∀ j ∈ T, ¬ incident i j) : min S.card T.card ≤ 3 := by
  by_cases hs : S.card ≤ 3
  · exact le_trans (min_le_left _ _) hs
  · obtain ⟨A, hAS, hA⟩ := Finset.exists_subset_card_eq (show 4 ≤ S.card by omega)
    have ht : T ⊆ avoid A := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => h i (hAS hi) j hj⟩
    exact (min_le_right _ _).trans ((Finset.card_le_card ht).trans (avoid_four_le_three A hA))

end Geometry8752
