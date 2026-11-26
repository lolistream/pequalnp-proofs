import Mathlib

namespace PlaneTests

theorem determine
    (R : Fin 13 → Fin 13 → Prop) (avoid : Finset (Fin 13) → Finset (Fin 13))
    (F : Finset (Fin 13) → Finset (Fin 13) → Bool)
    (symm : ∀ p l, R p l → R l p)
    (avoid_iff : ∀ S l, l ∈ avoid S ↔ ∀ p ∈ S, ¬ R p l)
    (small : ∀ S T : Finset (Fin 13), (∀ p ∈ S, ∀ l ∈ T, ¬ R p l) → S.card ≤ 3 ∨ T.card ≤ 3)
    (mono : ∀ {S T U V}, S ⊆ U → T ⊆ V → F S T = true → F U V = true)
    (onEdge : ∀ p l, R p l → F {p} {l} = true)
    (off : ∀ S : Finset (Fin 13), S.card ≤ 3 → F S (avoid S) = false ∧ F (avoid S) S = false)
    (S T : Finset (Fin 13)) : F S T = true ↔ ∃ p ∈ S, ∃ l ∈ T, R p l := by
  constructor
  · intro hon
    by_contra hn
    have hnone : ∀ p ∈ S, ∀ l ∈ T, ¬ R p l := fun p hp l hl hpl => hn ⟨p, hp, l, hl, hpl⟩
    rcases small S T hnone with hS | hT
    · have hsub : T ⊆ avoid S := fun l hl => (avoid_iff S l).2 (fun p hp => hnone p hp l hl)
      have hit : F S (avoid S) = true := mono (Finset.Subset.rfl : S ⊆ S) hsub hon
      simp [(off S hS).1] at hit
    · have hsub : S ⊆ avoid T := fun p hp => (avoid_iff T p).2 (fun l hl hlp => hnone p hp l hl (symm l p hlp))
      have hit : F (avoid T) T = true := mono hsub (Finset.Subset.rfl : T ⊆ T) hon
      simp [(off T hT).2] at hit
  · rintro ⟨p, hp, l, hl, hpl⟩
    exact mono (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl) (onEdge p l hpl)

end PlaneTests
