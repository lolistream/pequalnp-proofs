import RepresentativeLowerBounds
import RepresentativeUpperBounds
import RepSizePerm
import WorstCase

namespace PEqualNP.Rep35Selected

open PEqualNP.Represents AtlasLower

private def cols1091 : List W := [0x33333333333333fff00000000fff, 0x444444444444440000000ffff000, 0x88888888888888000ffff0000000, 0x999999999999990000000000f000, 0x66666666666666000000f0000000, 0xf00f000f000f, 0xf00f000f000f0, 0xf00f000f000f00]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem lower1091 : lower 1091 5 :=
  sound (k := 4) (xs := cols1091) (samp := sample 1091)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def cols3239 : List W := [0xe1c3870e1c38700000000003fff, 0x3060c183060c18000007ffffc000, 0xc183060c183060fffff800000000, 0x52a54a952a54a900000000000000, 0x850a142850a142000000001fc000, 0x2850a142850a140003f800000000, 0x1fc000fe0007f, 0xfe0007f0003f80]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem lower3239 : lower 3239 6 :=
  sound (k := 5) (xs := cols3239) (samp := sample 3239)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem lower7549 : lower 7549 9 := by
  intro s h
  by_contra hn
  obtain ⟨C, hm, hs, hr⟩ := h
  exact refute_MatrixRefutation3x5Mask7549Budget8 ⟨C, hm, hs.trans (show s ≤ 8 by omega), hr⟩

/-- (mask, minimum) pairs for which both directions are certified in this module. -/
def selected : List (ℕ × ℕ) := (1091, 5) :: (3239, 6) :: (7549, 9) :: AtlasLower.rows

private theorem selected_lower (p : ℕ × ℕ) (hp : p ∈ selected) : lower p.1 p.2 := by
  simp only [selected, List.mem_cons] at hp
  rcases hp with rfl | rfl | rfl | h
  · exact lower1091
  · exact lower3239
  · exact lower7549
  · exact AtlasLower.table_lower _ h

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
private theorem in_upper_table : ∀ p ∈ selected,
    p ∈ Rep35Upper.entries.map (fun e => (e.mask, e.budget)) := by decide +kernel

set_option maxRecDepth 16000 in
theorem selected_size : selected.length = 104 ∧ (selected.map Prod.fst).Nodup := by decide +kernel

/-- A size budget works for a listed representative exactly when it reaches the recorded minimum. -/
theorem budget_iff {m k : ℕ} (hmk : (m, k) ∈ selected) (s : ℕ) :
    RepSizeAtMost (AtlasLower.graph m) s ↔ k ≤ s := by
  constructor
  · exact selected_lower (m, k) hmk s
  · intro h
    obtain ⟨e, he, hp⟩ := List.mem_map.mp (in_upper_table (m, k) hmk)
    have hm : e.mask = m := congrArg Prod.fst hp
    have hk : e.budget = k := congrArg Prod.snd hp
    have hu : RepSizeAtMost (AtlasLower.graph e.mask) e.budget := Rep35Upper.entries_upper e he
    rw [hm, hk] at hu
    obtain ⟨C, hmono, hsize, hrep⟩ := hu
    exact ⟨C, hmono, hsize.trans h, hrep⟩

/-- The same minimum holds for every independent relabeling of the rows and columns. -/
theorem relabel_budget_iff {m k : ℕ} (hmk : (m, k) ∈ selected)
    (r : Equiv.Perm (Fin 3)) (c : Equiv.Perm (Fin 5)) (s : ℕ) :
    RepSizeAtMost (fun u v => AtlasLower.graph m (r u) (c v)) s ↔ k ≤ s :=
  (repSizeAtMost_perm_iff (AtlasLower.graph m) s r c).trans (budget_iff hmk s)

end PEqualNP.Rep35Selected
