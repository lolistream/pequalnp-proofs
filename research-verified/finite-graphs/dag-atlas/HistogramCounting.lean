import Mathlib

namespace PEqualNP.Rep35Histogram

private theorem card_le_sum_of_cover {X ι : Type*} (s : Finset X) (rows : List ι)
    (pieces : ι → Finset X) (w : ι → ℕ)
    (cover : ∀ x ∈ s, ∃ e ∈ rows, x ∈ pieces e)
    (bound : ∀ e ∈ rows, (pieces e).card ≤ w e) : s.card ≤ (rows.map w).sum := by
  classical
  induction rows generalizing s with
  | nil =>
    have hs : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => by simpa using cover x hx)
    simp [hs]
  | cons e es ih =>
    have rest : (s \ pieces e).card ≤ (es.map w).sum := by
      apply ih
      · intro x hx
        obtain ⟨hs, hn⟩ := Finset.mem_sdiff.mp hx
        obtain ⟨a,ha,hpiece⟩ := cover x hs
        rcases List.mem_cons.mp ha with rfl | ha
        · exact (hn hpiece).elim
        · exact ⟨a,ha,hpiece⟩
      · exact fun a ha => bound a (List.mem_cons_of_mem e ha)
    have sub : s ⊆ pieces e ∪ (s \ pieces e) := by
      intro x hx
      by_cases h : x ∈ pieces e
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx,h⟩)
    exact (Finset.card_le_card sub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (bound e List.mem_cons_self) rest))

/-- A finite cover whose upper weights sum to the size of the whole set has the exact
    indicated weight in each budget class. The rows are a list and may repeat. -/
theorem count_eq_weight {X : Type*} [Fintype X] {ι : Type*} (rows : List ι)
    (value : X → ℕ∞) (budget weight : ι → ℕ) (pieces : ι → Finset X)
    (cover : ∀ x, ∃ e ∈ rows, x ∈ pieces e)
    (correct : ∀ e ∈ rows, ∀ x ∈ pieces e, value x = (budget e : ℕ∞))
    (bound : ∀ e ∈ rows, (pieces e).card ≤ weight e)
    (total : (rows.map weight).sum = Fintype.card X) (k : ℕ) :
    Nat.card {x : X // value x = (k : ℕ∞)} =
      (rows.map (fun e => if budget e = k then weight e else 0)).sum := by
  classical
  have bucket (p : X → Prop) (q : ι → Prop) [DecidablePred p] [DecidablePred q]
      (uniform : ∀ e ∈ rows, ∀ x ∈ pieces e, p x ↔ q e) :
      (Finset.univ.filter p).card ≤ (rows.map (fun e => if q e then weight e else 0)).sum := by
    apply card_le_sum_of_cover _ _ (fun e => (pieces e).filter p)
    · intro x hx
      obtain ⟨e,he,hm⟩ := cover x
      exact ⟨e,he,Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hx).2⟩⟩
    · intro e he
      by_cases h : q e
      · simpa [h] using (Finset.card_filter_le (pieces e) p).trans (bound e he)
      · have empty : (pieces e).filter p = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hx
          exact h ((uniform e he x hm).mp hp)
        simp [empty,h]
  have eqv (e : ι) (he : e ∈ rows) (x : X) (hx : x ∈ pieces e) :
      value x = (k : ℕ∞) ↔ budget e = k := by rw [correct e he x hx, ENat.natCast_inj]
  have yes := bucket (fun x => value x = (k : ℕ∞)) (fun e => budget e = k) eqv
  have no := bucket (fun x => ¬(value x = (k : ℕ∞))) (fun e => budget e ≠ k)
    (fun e he x hx => not_congr (eqv e he x hx))
  have both := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
    (fun x => value x = (k : ℕ∞))
  rw [Finset.card_univ] at both
  have split (l : List ι) :
      (l.map (fun e => if budget e = k then weight e else 0)).sum +
      (l.map (fun e => if budget e ≠ k then weight e else 0)).sum = (l.map weight).sum := by
    induction l with
    | nil => simp
    | cons e es ih => by_cases h : budget e = k <;> simp [h] at * <;> omega
  have weights := split rows
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

end PEqualNP.Rep35Histogram
