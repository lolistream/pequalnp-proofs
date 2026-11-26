import AtlasClassification
import Complete1150
import Complete1278
import Complete3324
import Cut1126D5
import Cut1148D6
import Cut1231D6
import Cut1243D7
import Cut1274D7
import Cut1534D7
import Cut16123D7
import Cut3242D6
import Cut3320D6
import Cut3325D7
import Cut3502D6
import Cut3580D7
import Cut3581D7
import Cut3997D7
import Cut4030D7
import Cut7673D7
import Cut7998D7
import Cut8061D7
import LowerDirect1
import LowerDirect2
import LowerDirect3
import LowerDirect4
import MemoSmoke35
import NewHigh10
import NewHigh11
import NewHigh13
import NewHigh14
import NewHigh15
import NewHigh9
import NewMiddle1
import NewMiddle10
import NewMiddle3
import NewMiddle4
import NewMiddle6
import NewMiddle7
import NewMiddle9

namespace PEqualNP.Rep35Classification
open PEqualNP.Represents

private def singleRows : List (ℕ × ℕ) := [(35, 4), (3320, 8), (1148, 8), (3324, 9), (1278, 9), (1150, 9), (7998, 9), (8061, 9), (3502, 8), (4030, 9), (16123, 9), (1126, 7), (3580, 9), (7673, 9), (3997, 9), (3242, 8), (3581, 9), (1231, 8), (1534, 9), (3325, 9), (1274, 9), (1243, 9)]
private theorem singleProof : LowerTable singleRows := by
  intro p hp
  simp only [singleRows, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact MemoRow35.result
  · exact AtlasCutRow3320D6.result
  · exact AtlasCutRow1148D6.result
  · exact AtlasCutRow3324D7.result
  · exact AtlasCutRow1278D7.result
  · exact AtlasCutRow1150D7.result
  · exact AtlasCutRow7998D7.result
  · exact AtlasCutRow8061D7.result
  · exact AtlasCutRow3502D6.result
  · exact AtlasCutRow4030D7.result
  · exact AtlasCutRow16123D7.result
  · exact AtlasCutRow1126D5.result
  · exact AtlasCutRow3580D7.result
  · exact AtlasCutRow7673D7.result
  · exact AtlasCutRow3997D7.result
  · exact AtlasCutRow3242D6.result
  · exact AtlasCutRow3581D7.result
  · exact AtlasCutRow1231D6.result
  · exact AtlasCutRow1534D7.result
  · exact AtlasCutRow3325D7.result
  · exact AtlasCutRow1274D7.result
  · exact AtlasCutRow1243D7.result

private def blocks : List (List (ℕ × ℕ)) :=
  [Rep35Selected.selected, LowerDirect1.rows, LowerDirect2.rows, LowerDirect3.rows, LowerDirect4.rows, NewHigh10.rows, NewHigh11.rows, NewHigh13.rows, NewHigh14.rows, NewHigh15.rows, NewHigh9.rows, NewMiddle1.rows, NewMiddle10.rows, NewMiddle3.rows, NewMiddle4.rows, NewMiddle6.rows, NewMiddle7.rows, NewMiddle9.rows, singleRows]
private theorem sound_blocks : ∀ b ∈ blocks, LowerTable b := by
  intro b h
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact already_selected
  · exact LowerDirect1.checked
  · exact LowerDirect2.checked
  · exact LowerDirect3.checked
  · exact LowerDirect4.checked
  · exact NewHigh10.checked
  · exact NewHigh11.checked
  · exact NewHigh13.checked
  · exact NewHigh14.checked
  · exact NewHigh15.checked
  · exact NewHigh9.checked
  · exact NewMiddle1.checked
  · exact NewMiddle10.checked
  · exact NewMiddle3.checked
  · exact NewMiddle4.checked
  · exact NewMiddle6.checked
  · exact NewMiddle7.checked
  · exact NewMiddle9.checked
  · exact singleProof

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem covered : ∀ p ∈ catalogue, p ∈ blocks.flatten := by decide +kernel

theorem all_lower : LowerTable catalogue := by
  intro p hp
  obtain ⟨b, hb, hpb⟩ := List.mem_flatten.mp (covered p hp)
  exact sound_blocks b hb p hpb

theorem entry_budget_iff (e : Rep35Upper.Entry) (he : e ∈ Rep35Upper.entries) (s : ℕ) :
    RepSizeAtMost (AtlasLower.graph e.mask) s ↔ e.budget ≤ s := by
  have h : (e.mask, e.budget) ∈ catalogue := List.mem_map.mpr ⟨e, he, rfl⟩
  exact budget_of_lower h (all_lower _ h) s

/-- Every labeled 3×5 relation has an atlas representative with the same exact minimum. -/
theorem exact_classification (A : Fin 3 → Fin 5 → Bool) :
    ∃ e ∈ Rep35Upper.entries, ∃ r : Equiv.Perm (Fin 3), ∃ c : Equiv.Perm (Fin 5),
      (∀ i j, A i j = AtlasLower.graph e.mask (r i) (c j)) ∧
      (∀ s, RepSizeAtMost A s ↔ e.budget ≤ s) ∧ repSize A = (e.budget : ℕ∞) :=
  classify_of_lower all_lower A

end PEqualNP.Rep35Classification
