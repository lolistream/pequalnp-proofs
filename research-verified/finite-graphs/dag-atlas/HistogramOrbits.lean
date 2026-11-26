import Mathlib

namespace PEqualNP.Rep35Histogram

abbrev Matrix := Fin 3 → Fin 5 → Bool
abbrev Sym := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)

def move (g : Sym) (A : Matrix) : Matrix := fun i j => A (g.1 i) (g.2 j)

noncomputable def orbit (A : Matrix) : Finset Matrix := by
  classical
  exact Finset.univ.image (fun g : Sym => move g A)

theorem move_mem (g : Sym) (A : Matrix) : move g A ∈ orbit A := by
  classical
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩

private theorem representative (A : Matrix) (B : ↥(orbit A)) :
    ∃ g : Sym, move g A = B.val := by
  classical
  obtain ⟨g, _, hg⟩ := Finset.mem_image.mp B.property
  exact ⟨g, hg⟩

private theorem sym_card : Fintype.card Sym = 720 := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
  decide

/-- Each orbit element has at least as many distinct preimages as any supplied set of fixing permutations. -/
theorem orbit_bound (A : Matrix) {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → Sym)
    (hinj : Function.Injective f) (fixed : ∀ i ∈ s, move (f i) A = A)
    {w : ℕ} (positive : 0 < s.card) (mul : w * s.card = 720) : (orbit A).card ≤ w := by
  classical
  choose rep hrep using representative A
  let pack : ↥(orbit A) × ↥s → Sym := fun p => f p.2.val * rep p.1
  have recover (B : ↥(orbit A)) (i : ↥s) : move (pack (B, i)) A = B.val := by
    change move (rep B) (move (f i.val) A) = B.val
    rw [fixed i.val i.property, hrep B]
  have unique : Function.Injective pack := by
    rintro ⟨B, i⟩ ⟨C, j⟩ heq
    have hBC : B = C := Subtype.ext ((recover B i).symm.trans ((congrArg (fun g => move g A) heq).trans (recover C j)))
    subst C
    have hij : f i.val = f j.val := mul_right_cancel (show f i.val * rep B = f j.val * rep B from heq)
    have hij' : i = j := Subtype.ext (hinj hij)
    subst j
    rfl
  have hcard := Fintype.card_le_of_injective pack unique
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, sym_card, ← mul] at hcard
  exact Nat.le_of_mul_le_mul_right hcard positive

theorem mem_orbit_iff (x A : Matrix) : x ∈ orbit A ↔ ∃ g : Sym, x = move g A := by
  classical
  constructor
  · intro hx
    obtain ⟨g, _, hg⟩ := Finset.mem_image.mp hx
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    exact move_mem g A

end PEqualNP.Rep35Histogram
